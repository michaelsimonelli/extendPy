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
.py.ut.logger:{-1 (string .z.z)," ", x};
.py.ut.isAtom:{ (0h > type x) and (-20h < type x) };
.py.ut.isList:{ (0h <= type x) and (20h > type x) };
.py.ut.enlist:{ $[not .py.ut.isList x;enlist x; x] };
.py.ut.isDict:{ $[99h = type x;not .py.ut.isTabl x; 0b] };
.py.ut.strSym:{ if[any {(type x) in ((5h$til 20)_10),98 99h}@\:x; :.z.s'[x]]; $[10h = abs type x; `$x; x] };
.py.ut.isNull:{ $[.py.ut.isAtom[x] or .py.ut.isList[x] or x ~ (::); $[.py.ut.isGLst[x]; all .py.ut.isNull each x; all null x]; .py.ut.isTabl[x] or .py.ut.isDict[x];$[count x;0b;1b];0b ] };

.py.meta.:(::);

.py.modules:()!();

.py.moduleInfo:.p.get[`module_info;<];

///
// Import a python module
//
// parameters:
// module [symbol] - module name
// as     [symbol] - alias to avoid clashes
.py.import:{[module] 
  if[module in key .py.modules;
    .py.ut.logger"Module already imported"; :(::)];
  if[@[{.py.modules[x]:.p.import x; 1b}; module; .py.importError[module]];
      .py.ut.logger"Imported python module '",string[module],"'"];
  };

.py.importError:{[module; error]
  -1"Python module '",string[module],"' failed with: ", "(",error,")";
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
  pyModule: .py.modules[module];
  modInfo: .py.moduleInfo[pyModule];
  clsInfo: modInfo[`classes];
  project: .py.priv.project[pyModule; clsInfo];
  (` sv `,module ) set project;
  .py.meta[module]:modInfo;
  1b};

///
// Maps python module functions to callable q functions
// Mapped functions are stored in respective module context in .pq namespace
//
// parameters:
// module [symbol]    - module to map from (must be imported)
// module [list(sym)] - list of functions to map
.py.map:{[module; functions; as]
  pyModule:.py.modules[module];
  qRef:$[.py.ut.isNull as;module;as];

  if[not (.py.ut.isDict .py[qRef]) and (first .py[qRef]~(::));
    .py[qRef]:enlist[`]!enlist[::]];

  mapping:functions!pyModule[;<]@'hsym functions;
  .py[qRef],:mapping;
  };

///
// Creates a pseudo generator callable in q
//
// parameters:
// func     [symbol]  - type of generator, accepts: list or next
//  list - returns the entire iterator as one object
//  next - returns the next object in the iterator
//  (type dependent on iterator, next is callable until iterator exhausted)
// iterator [foreign] - embedPy iterator
// nul      [null]    - null param to prevent function from executing
.py.generate:{[func;generator;nul]
  res:.py.builtins[func;generator];
  res};

///
// Create some useful embedPy tools
.py.ini:`$"__init__";

.py.none:.p.eval"None"; 

.py.isNone:{x~.py.none};

.py.import[`builtins];

.py.map[`builtins;`list`next`vars`str;`];

.py.peta:{[m;c;f] .py.meta[m; `classes; c; `attributes; `functions; f;`parameters]};

///////////////////////////////////////
// PRIVATE CONTEXT                   //
///////////////////////////////////////

.py.priv.project:{[imp; cls]
  p: .py.ut.eachKV[cls;{
      obj: x hsym y;
      atr: z`attributes;
      cxt: .py.priv.context[obj; atr];
      cxt}[imp]];
  p};

.py.priv.context:{[obj; atr; args]
  data: atr`data;
  prop: atr`properties;
  func: atr`functions;

  init: func[.py.ini];
  params: init[`parameters];
  required: params[::;`required];

  if[(args~(::)) and (any required);
    '"Missing required parameters: ",", " sv string where required];

  args: .py.priv.args[args];
  apply: $[1<count args;.;@];
  inst: apply[obj;args];

  func _: .py.ini;
  vars: .py.builtins.vars[inst];
  docs: enlist[`]!enlist[::];

  if[count data; docs[`data]: data];
  if[count prop; docs[`prop]: prop];
  if[count func; docs[`func]: func];
  if[count vars; docs[`vars]: vars];

  mD: .py.priv.mapData[inst; data];
  mP: .py.priv.mapProp[inst; prop];
  mF: .py.priv.mapFunc[inst; func];
  mV: .py.priv.mapVars[inst; vars];
  cx: enlist[`]!enlist[::];
  cx: mD,mP,mF,mV;
  cx[`docs_]:docs;
  cx};

// .py.priv.wrapper:{[obj; atr; args]
//   data: atr`data;
//   prop: atr`properties;
//   func: atr`functions;
//
//   init: func[.py.ini];
//   params: init[`parameters];
//   required: params[::;`required];
//
//   if[(args~(::)) and (any required);
//     '"Missing required parameters: ",", " sv string where required];
//
//   args: .py.priv.args[args];
//   apply: $[1<count args;.;@];
//   inst: apply[obj;args];
//
//   func _: .py.ini;
//   vars: .py.builtins.vars[inst];
//   docs: enlist[`]!enlist[::];
//
//   if[count data; docs[`data]: data];
//   if[count prop; docs[`prop]: prop];
//   if[count func; docs[`func]: func];
//   if[count vars; docs[`vars]: vars];
//
//   mD: .py.priv.mapData[inst; data];
//   mP: .py.priv.mapProp[inst; prop];
//   mF: .py.priv.mapFunc[inst; func];
//   mV: .py.priv.mapVars[inst; vars];
//   cx: enlist[`]!enlist[::];
//   cx: mD,mP,mF,mV;
//   cx[`docs_]:docs;
//   cx};


.py.priv.args:{[args]
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

.py.priv.mapData:{[obj; d]
  k: key d;
  v: obj@'hsym k;
  m: k!v;
  m};

.py.priv.mapProp:{[ins; d]
  m: .py.ut.eachKV[d;{
      h: hsym y;
      d: (enlist `get)!(enlist x[h;]);
      if[z`setter; d[`set]:x[:;h;]];
      .py.priv.acor[d]}[ins]];
  m};

.py.priv.mapFunc:{[ins; d]
  f: key d;
  m: f!ins[;<]@'hsym f;
  m};

.py.priv.mapVars:{[ins; d]
  k: key d;
  h: hsym k;
  v:{ g: x[y;];
      s: x[:;y;];
      d:`get`set!(g;s);
      .py.priv.acor[d]}[ins;] each h;
  m: (!/)($[1>=count k; .py.ut.enlist each;](k;v));
  m};

.py.priv.acor:{[acor;arg]
  typ:$[arg~(::);[arg:`;`get];`set];
  if[.py.ut.isNull func:acor[typ];'string[typ]," accessor not available"];
  func[arg]};