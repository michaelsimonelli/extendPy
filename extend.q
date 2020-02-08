///
// extendPy
//
// Extends embedPy
// - reflection
//   *inspect python objects
//   *map python functions to native q
//   *emulate python module to q context (function library)
// - helper & utility functions
//   *.p.import wrapper
//   *
// ____________________________________________________________________________

// Load embedPy and the reflection module
\l p.q
\l reflect.p

///////////////////////////////////////
// GENERIC UTILITY                   //
///////////////////////////////////////

.ut.eachKV:{ key [x]y'x};
.ut.exists:{ @[{not () ~ key x}; x; 0b] };
.ut.enlist:{ $[not .ut.isList x;enlist x; x] };
.ut.isAtom:{ (0h > type x) and (-20h < type x) };
.ut.isList:{ (0h <= type x) and (20h > type x) };
.ut.assert:{ [x;y] if[not x;'"Assert failed: ",y] };
.ut.isDict:{ $[99h = type x;not .ut.isTable x; 0b] };
.ut.isName:{ if[not .ut.exists x; :0b]; v:value x; (.ut.isDict v) and (::) ~ first v };
.ut.isNull:{ $[.ut.isAtom[x] or .ut.isList[x] or x ~ (::); $[.ut.isGList[x]; all .ut.isNull each x; all null x]; .ut.isTable[x] or .ut.isDict[x];$[count x;0b;1b];0b ] };
.ut.strSym:{ if[any {(type x) in ((5h$til 20)_10),98 99h}@\:x; :.z.s'[x]]; $[10h = abs type x; `$x; x] };
.ut.isTable:{ .Q.qt x };
.ut.isGList:{ 0h = type x };
.ut.blankNS:enlist[`]!enlist(::);
.ut.default:{ $[.ut.isNull x; y; x]};
.ut.xfunc:{ (')[x; enlist] };
.ut.xposi:{ .ut.assert[not .ut.isNull x y; "positional argument (",(y$:),") '",(z$:),"' required"]; x y};

///////////////////////////////////////
// IMPORT WRAPPER                    //
///////////////////////////////////////

// Stores imported python modules
.py.modules: ()!();

///
// Import a python module
//
// parameters:
// module [symbol] - module name
// as     [symbol] - alias to avoid clashes
.py.import:{[module] 
  if[module in key .py.modules;
    .py.lg"Module already imported"; :(::)];
  if[@[{.py.modules[x]:.p.import x; 1b}; module; .py.err.import[module]];
      .py.lg"Imported module '",(module$:),"'"];
  };

.py.err.import:{[module; error]
  .py.lg"ERROR - Import module '",(module$:),"' failed with: ", "(",error,")";
  0b};

///////////////////////////////////////
// REFLECTION CONTEXT                //
///////////////////////////////////////

// Stores reflected modules
.py.reflection.dir: .ut.blankNS;

// Gets python module info nested dict
.py.reflection.getInfo: .p.get[`get_info;<];

// Drill down meta info for module, class, function
.py.reflection.meta: .ut.xfunc {[x]
  m: .ut.xposi[x; 0; `module];
  c: .ut.default[x 1; `];
  f: .ut.default[x 2; `];

  r: .py.reflection.dir[m; `classes];

  if[not .ut.isNull c; r: r[c]`functions];

  if[not .ut.isNull f; r: r f];

  r};

///
// Emulate a q context from a python module.
// The context is a full representation of the python module completely callable in q.
// A context is generally made up of 'classes', but can also include functions and variables.
// A 'class' can be initialed according to its __init__ method, returning fully callable function library (dictionary).
// This library maintains a reference to the underlying python instance, and replicates that same behavior in q.
//
// parameters:
// module [symbol] - module to reflect (must be imported)
// cxt [symbol] - context (namespace) to set functions, defaults to module name
.py.reflection.emulate: .ut.xfunc {[x]
  module: .ut.xposi[x; 0; `module];
  cxt: .ut.default[x 1; module];

  reflected: .[{[module; cxt]
    .ut.assert[not .ut.isNull pyModule: .py.modules[module]; "Python module '",(module$:),"' must be imported first"];
    
    ref: .py.reflection.dir[module]: mi: .py.reflection.getInfo[pyModule];

    projection: (key mi`classes)!.py.reflection.priv.project[module] each key mi`classes;

    if[`data in key ref;
      projection,:.py.reflection.priv.data.cxt[pyModule; ref`data]];

    if[`functions in key ref;
      projection,:.py.reflection.priv.functions.cxt[pyModule; ref`functions]];

    $["." = first string cxt; cxt; (` sv `,cxt)] set projection;

    1b}; (module; cxt); .py.err.emulate[module]];

  if[reflected;
    .py.lg"Reflected module '",(module$:),"' to `",(cxt$:), " context"];
  };

.py.err.emulate:{[module;error]
  .py.lg"ERROR - Module emulate '",(module$:),"' failed with: ", "(",error,")";
  0b};

///
// Maps python module functions to callable q functions
// Mapped functions are stored in respective module context in .pq namespace
//
// parameters:
// module [symbol, required] - imported python module
// funcs [list(sym), required] - list of module functions
// cxt [symbol] - context (namespace) to set functions, defaults to `.py
.py.reflection.map: .ut.xfunc {[x]
  module: .ut.xposi[x; 0; `module];
  funcs: .ut.xposi[x; 1; `funcs];
  cxt: .ut.default[x 2; `.py];

  mapped: .[{[module; funcs; cxt]
    .ut.assert[not .ut.isNull pyModule:.py.modules[module]; "Python module '",(module$:),"' must be imported first"];
  
    qCallable: .py.qcall[pyModule] funcs;

    if[not .ut.isName cxt;
      cxt set (!/)((`;(::)),:')];
    
    @[cxt; funcs; :; qCallable];
  
    1b}; (module; funcs; cxt); .py.err.map[module; funcs]];

  if[mapped;
    .py.lg"Mapped functions (",(module$:),"; ",(", " sv (funcs$:)),") in `",(cxt$:), " context"];
  };

.py.err.map:{[module; funcs; error]
  .py.lg"ERROR - Function mapping (",(module$:),"; ",(", " sv (funcs$:)),") failed with: ", "(",error,")";
  0b};

.py.reflection.priv.project:{[module; class]
  obj: .py.modules[module] hsym class;
  atr: .py.reflection.dir[module][`classes][class];
  pro: .ut.xfunc {[x;y] x[y]}[.py.reflection.priv.context[obj; atr]];
  pro};

.py.reflection.priv.context:{[obj; atr; arg]
  init: atr[`functions][`$"__init__"];
  params: init[`parameters];
  required: params[::;`required];

  if[(arg~(::)) and (any required);
    '"Missing required parameters: ",", " sv string where required];

  blk: .ut.blankNS;
  arg: .py.reflection.priv.args[arg];
  ins: $[1<count arg;.;@][obj;arg];

  atr[`vars]: .py.vars[ins];
  atr: @[atr;`functions;{x _ `$"__init__"}];

  cxt: blk,(,/)value .ut.eachKV[`doc _ atr;{.py.reflection.priv[y;`cxt][x;z]}[ins]];

  cxt};

.py.reflection.priv.args:{[args]
  if[args~(::);:args];
  
  args: .ut.strSym[args];

  if[.ut.isDict args;
    if[10h = type key args;
      args:({`$x} each key args)!value args];
    ]; 

  args: $[.ut.isDict args; pykwargs args; 
          (.ut.isGList args) and (.ut.isDict last args);
            (pyarglist -1 _ args; pykwargs last args); 
              pyarglist args];
  args};

.py.reflection.priv.data.cxt:{[ins; info]
  dkey: key info;
  dval: ins@'hsym dkey;
  cxt: dkey!dval;
  cxt};

.py.reflection.priv.properties.cxt:{[ins; info]
  cxt: .ut.eachKV[info; 
    {[ins; name; prop]
      hpy: hsym name;
        gsm: (enlist `get)!(enlist ins[hpy;]);
          if[prop`setter; gsm[`set]:ins[:hpy;]];
            prj:.py.reflection.priv.properties.project[gsm];
              prj} ins];
  cxt};

.py.reflection.priv.properties.project:{[qco; arg]
  acc: $[arg~(::); [arg:`; `get]; `set];

  if[.ut.isNull func:qco[acc];
    'string[typ]," accessor not available"];

  res:func[arg];

  res}

.py.reflection.priv.functions.cxt:{[ins; info]
  fns: (key info) except `$"__init__";
  cxt: fns!{[ins;fn]
        prj:.py.qcall[ins;] fn;
          prj}[ins] each fns;
  cxt};

/ .py.reflection.func.prj:{[qco; arg]
/   arg: .ut.enlist $[.ut.isNull arg; (::); arg];
/   res: qco . arg;
/   res};

.py.reflection.priv.vars.cxt:{[ins; info]
  vkey: key info;
  vpns: hsym vkey;
  vmap: {[ins; vpn] 
          gtf: ins[vpn;];
            stf: ins[:;vpn;];
              gsm: `get`set!(gtf;stf);
                prj:.py.reflection.priv.properties.project[gsm];
                  prj}[ins;] each vpns;
  cxt: (!/)($[1>=count vkey; .ut.enlist each;](vkey;vmap));
  cxt};


///
// Port some useful python built-in functions

.py.none: .p.eval"None"; 

.py.lg:{ -1 (string .z.z)," [Py] ", x};

.py.isNone:{x~.py.none};

.py.qcall:{.p.qcallable[x hsym y]}';

.py.import[`builtins];

.py.reflection.map[`builtins;`list`next`vars`str];
