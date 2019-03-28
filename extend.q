///
// extendPy
//
// Extends embedPy
// - provides dynamic module import
// - maps python module->class->functions to a native q context/function library
// ____________________________________________________________________________

\l p.q
\l reflect.p

.py.ut.isTabl:{ .Q.qt x };
.py.ut.eachKV:{ key [x]y'x};
.py.ut.isGLst:{ 0h = type x };
.py.ut.logger:{ -1 (string .z.z)," [Py] ", x};
.py.ut.exists:{ @[{not () ~ key x}; x; 0b] };
.py.ut.isAtom:{ (0h > type x) and (-20h < type x) };
.py.ut.isList:{ (0h <= type x) and (20h > type x) };
.py.ut.enlist:{ $[not .py.ut.isList x;enlist x; x] };
.py.ut.isDict:{ $[99h = type x;not .py.ut.isTabl x; 0b] };
.py.ut.isName:{ if[not .py.ut.exists x; :0b]; v:value x; (.py.ut.isDict v) and (::) ~ first v };
.py.ut.strSym:{ if[any {(type x) in ((5h$til 20)_10),98 99h}@\:x; :.z.s'[x]]; $[10h = abs type x; `$x; x] };
.py.ut.isNull:{ $[.py.ut.isAtom[x] or .py.ut.isList[x] or x ~ (::); $[.py.ut.isGLst[x]; all .py.ut.isNull each x; all null x]; .py.ut.isTabl[x] or .py.ut.isDict[x];$[count x;0b;1b];0b ] };

.py.mods: ()!();

.py.none: .p.eval"None"; 

.py._init_: `$"__init__";

.py.ref: (!/)((`;(::)),:');

.py.info: .p.get[`get_info;<];

.py.isNone:{x~.py.none};

.py.qcall:{.p.qcallable[x hsym y]}';

.py.metaFunc:{[m;c] .py.ref[m; `classes; c; `attributes; `functions]};

.py.metaParam:{[m;c;f] .py.ref[m; `classes; c; `attributes; `functions; f; `parameters]};

// Import a python module
//
// parameters:
// module [symbol] - module name
// as     [symbol] - alias to avoid clashes
.py.import:{[module] 
  if[module in key .py.mods;
    .py.ut.logger"Module already imported"; :(::)];
  if[@[{.py.mods[x]:.p.import x; 1b}; module; .py.err.import[module]];
      .py.ut.logger"Imported module '",(module$:),"'"];
  };

.py.err.import:{[module; error]
  .py.ut.logger"ERROR! Import module '",(module$:),"' failed with: ", "(",error,")";
  0b};

///
// Reflect a python module into kdb context
// Creates a context in the .pq name space
// Context root is a dictionary of class_name->projection
// The projection is a callable init function returning a function library
// Library is a callable dictionary of function_name->embedPy function
//
// parameters:
// module [symbol] - module to reflect (must be imported)
.py.reflect:{[module]
  iModule: .py.mods[module];
  modInfo: .py.info[iModule];
  qProject: .py.rt.project[iModule; modInfo`classes];

  (` sv `,iModule ) set qProject;
  .py.ref[module]:modInfo;

  1b};

///
// Maps python module functions to callable q functions
// Mapped functions are stored in respective module context in .pq namespace
//
// parameters:
// module [symbol]    - module to map from (must be imported)
// module [list(sym)] - list of functions to map
.py.map:{[module; functions; context]
  mapped: .[{iModule: $[x in key .py.mods;
                        .py.mods[x];
                          '"Python module '",(x$:),"' must be imported first"];

              qMapping: .py.qcall[iModule] y;

                rContext: $[.py.ut.isNull z; x; z];
    
                if[not .py.ut.isName rContext;
                  rContext set (!/)((`;(::)),:')];
    
                  @[rContext; y; :; qMapping]; 1b};

        (module; functions; context);

      .py.err.map[module;functions]];

  if[mapped;
    .py.ut.logger"Mapped '",(module$:),"' functions (",(", " sv (functions$:)),") in `",(context$:)];
  };
    
.py.err.map:{[module; functions; error]
  .py.ut.logger"ERROR! Map '",(module$:),"' functions (",(", " sv (functions$:)),") failed with: ", "(",error,")";
  0b};


///
// Port some useful python builtins
.py.import[`builtins];

.py.map[`builtins;`list`next`vars`str;`.py];

///////////////////////////////////////
// PRIVATE CONTEXT                   //
///////////////////////////////////////

.py.rt.project:{[imp; cls]
  p: .py.ut.eachKV[cls;{
      obj: x hsym y;
      atr: z`attributes;
      cxt: .py.rt.context[obj; atr];
      cxt}[imp]];
  p};

.py.rt.context:{[obj; atr; arg]
  data: atr`data;
  prop: atr`properties;
  func: atr`functions;

  init: func[.py._init_];
  params: init[`parameters];
  required: params[::;`required];

  if[(arg~(::)) and (any required);
    '"Missing required parameters: ",", " sv string where required];

  arg: .py.rt.args[arg];
  ins: $[1<count arg;.;@][obj;arg];

  func _: .py.ini;
  vars: .py.builtins.vars[ins];
  docs: .py.ut.ns;

  if[count data; docs[`data]: data];
  if[count prop; docs[`prop]: prop];
  if[count func; docs[`func]: func];
  if[count vars; docs[`vars]: vars];

  cxD: .py.rt.data.cxt[ins; data];
  cxP: .py.rt.prop.cxt[ins; prop];
  cxF: .py.rt.func.cxt[ins; func];
  cxV: .py.rt.vars.cxt[ins; vars];
  cxt: .py.ut.ns,cxD,cxP,cxF,cxV;
  
  cxt[`docs_]: docs;

  cxt};

.py.rt.args:{[args]
  if[args~(::);:args];
  
  args: .py.ut.strSym[args];

  if[.py.ut.isDict args;
    if[10h = type key args;
      args:({`$x} each key args)!value args];
    ]; 

  args: $[.py.ut.isDict args; pykwargs args; 
          (.py.ut.isGLst args) and (.py.ut.isDict last args);
            (pyarglist -1 _ args; pykwargs last args); 
              pyarglist args];
  args};

.py.rt.data.cxt:{[ins; info]
  dkey: key info;
  dval: ins@'hsym dkey;
  cxt: dkey!dval;
  cxt};

.py.rt.prop.cxt:{[ins; info]
  cxt: .py.ut.eachKV[info; 
    {[ins; name; prop]
      hpy: hsym name;
        gsm: (enlist `get)!(enlist ins[hpy;]);
          if[prop`setter; gsm[`set]:ins[:hpy;]];
            prj:.py.rt.prop.prj[gsm];
              prj} ins];
  cxt};

.py.rt.prop.prj:{[qco; arg]
  acc: $[arg~(::); [arg:`; `get]; `set];

  if[.py.ut.isNull func:qco[acc];
    'string[typ]," accessor not available"];

  res:func[arg];

  res}

.py.rt.func.cxt:{[ins; info]
  fns: key info;
  cxt: fns!{[ins;fn]
        prj:.py.qcall[ins;] fn;
          prj}[ins] each fns;
  cxt};

.py.rt.func.prj:{[qco; arg]
  arg: .py.ut.enlist $[.py.ut.isNull arg; (::); arg];
  res: qco . arg;
  res};

.py.rt.vars.cxt:{[ins; info]
  vkey: key info;
  vpns: hsym vkey;
  vmap: {[ins; vpn] 
          gtf: ins[vpn;];
            stf: ins[:;vpn;];
              gsm: `get`set!(gtf;stf);
                prj:.py.rt.prop.prj[gsm];
                  prj}[ins;] each vpns;
  cxt: (!/)($[1>=count vkey; .py.ut.enlist each;](vkey;vmap));
  cxt};
