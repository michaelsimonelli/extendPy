import io
import pyment
import builtins
from enum import IntEnum
from inspect import *
from collections import namedtuple, OrderedDict


# Python q reflection functions.
#
# Utility module for py.q embedPy framework.
# Provides metadata and type information for imported python modules


def get_info(obj):
    return _info(obj)


#############################
# Internal Functions - not to be used in kdb
#############################


Element = namedtuple('Element', 'name desc ptyp')


def get_attr(obj, predicate=None):
    attr = []
    members = getmembers(obj, predicate)
    for m in members:
        name = m[0]
        obj = m[1]
        typ = type(obj)
        if not _is_pub(name):
            continue
        if isroutine(obj):
            prof = 'function'
        elif isclass(obj):
            prof = 'class'
        elif ismodule(obj):
            prof = 'module'
        elif _is_primitive(obj):
            prof = 'data'
        else:
            prof = 'undef'
        entry = dict(name=name, prof=prof, obj=obj)
        attr.append(entry)
    return attr


class MemberGroup(IntEnum):
    MODULE = 0,
    CLASS = 1,
    DATA = 2,
    PROPERTY = 3,
    FUNCTION = 4,
    UNDEF = 5


class AttributeType(IntEnum):
    CLASS_VARIABLE = 0,
    INIT = 1,
    PROPERTY = 2,
    INSTANCE_METHOD = 3,
    CLASS_METHOD = 4,
    STATIC_METHOD = 5,
    BASE_METHOD = 6,
    BUILTIN_METHOD = 7


class Member:
    def __init__(self, obj, name=None, parent=None):
        self.obj = obj
        self.name = name
        self.parent = parent
        if not self.name:
            self.name = _obj_name(obj)
        self.doc = _obj_doc(self.obj)
        self.typ = type(self.obj)
        self.mod = _obj_mod(self.obj)
        self.grp = _obj_group(self.obj)
        try:
            self.cls = _obj_cls(self.obj)
        except AttributeError:
            self.cls = None
    
    def qmap(self):
        mem = self.name
        obj = self.obj
        typ = _obj_out(self.typ)
        cls = _obj_out(self.cls)
        mod = _obj_out(self.mod)
        qd = {'q': dict(mem=mem, typ=typ[0], cls=cls[0], mdl=mod[0])}
        pd = {'p': dict(mem=obj, typ=typ[1], cls=cls[1], mdl=mod[1])}
        qd.update(pd)
        return qd
    
    def get_members(self, predicate=None):
        return [Member(m[1], m[0], self.grp) for m in getmembers(self.obj, predicate)]
    
    def get_modules(self):
        return [m for m in self.get_members(ismodule) if _is_pub(c.name)]
    
    def get_classes(self):
        return [c for c in self.get_members(isclass) if _is_pub(c.name)]
    
    def get_data(self):
        if self.grp == MemberGroup.CLASS:
            data_info = [DataInfo(a) for a in classify_class_attrs(self.obj)
                         if _is_pub(a.name) and a.kind is 'data']
            return data_info
        if self.grp == MemberGroup.MODULE:
            data_info = []
            members = self.get_members()
            for m in members:
                if not _is_pub(m.name):
                    continue
                if m.grp == MemberGroup.DATA:
                    kind = 'data'
                    base = _obj_cls(m.obj)
                    info = DataInfo(Attribute(m.name, kind, base, m.obj))
                    data_info.append(info)
            return data_info
        return None
    
    def get_methods(self):
        if self.grp == MemberGroup.CLASS:
            method_info = [FuncInfo(a) for a in classify_class_attrs(self.obj)
                           if _is_pub(a.name) and 'method' in a.kind]
            return method_info
        if self.grp == MemberGroup.MODULE:
            method_info = []
            members = self.get_members(isroutine)
            for m in members:
                if not _is_pub(m.name):
                    continue
                if m.grp == MemberGroup.FUNCTION:
                    kind = 'builtin method' if isbuiltin(m.obj) else 'base method'
                    info = FuncInfo(Attribute(m.name, kind, self.obj, m.obj))
                    method_info.append(info)
            return method_info
        return None
    
    def get_properties(self):
        if self.grp == MemberGroup.CLASS:
            property_info = [PropertyInfo(a) for a in classify_class_attrs(self.obj)
                             if _is_pub(a.name) and a.kind is 'property']
            return property_info
        return None


class AttrInfo(Member):
    _kind_map = {
        'data':           AttributeType.CLASS_VARIABLE,
        'property':       AttributeType.PROPERTY,
        'method':         AttributeType.INSTANCE_METHOD,
        'class method':   AttributeType.CLASS_METHOD,
        'static method':  AttributeType.STATIC_METHOD,
        'base method':    AttributeType.BASE_METHOD,
        'builtin method': AttributeType.BUILTIN_METHOD
    }
    
    def __init__(self, attr: Attribute):
        super().__init__(attr.object, attr.name)
        self.def_class = attr.defining_class
        self.attr_kind = attr.kind
        
        if attr.name is '__init__':
            _attr_type = AttributeType.INIT
        else:
            _attr_type = self._kind_map[attr.kind]
            if attr.name.startswith('_'):
                self.exposed = False
        
        self.attr_type = _attr_type
        self.properties = {}
    
    def cxt(self):
        kind = self.attr_type.name.lower()
        meta = {'kind': kind, **self.properties, 'doc': self.doc}
        return meta


class DataInfo(AttrInfo):
    def __init__(self, attr: Attribute):
        super().__init__(attr)
        self.pval = self.obj
        self.ptyp = _obj_name(type(self.pval))
        self.properties = dict(pval=self.pval, ptyp=self.ptyp)


class PropertyInfo(AttrInfo):
    def __init__(self, attr: Attribute):
        super().__init__(attr)
        prop = self.obj
        accessors = dict(getter='fget', setter='fset')
        self.properties = {k: not not getattr(prop, v) for k, v in accessors.items()}


class FuncInfo(AttrInfo):
    def __init__(self, attr: Attribute):
        super().__init__(attr)
        self.signature = None
        self.document = None
        self.parameters = {}
        self.returns = {}
        self.properties = dict(parameters={}, returns={})
        if self.func:
            self.profile()
    
    @property
    def func(self):
        if callable(self.obj):
            return self.obj
        if hasattr(self.obj, '__func__'):
            return self.obj.__func__
    
    def profile(self):
        try:
            self.signature = signature(self.func)
        except ValueError:
            return
        
        self.document = _doc_meta(self.func)
        
        _parameters = {}
        param_meta = self.document.get('params', None)
        for param in self.signature.parameters.values():
            if param.name is 'self':
                continue
            
            param_info = ParamInfo(param)
            if param_meta and param.name in param_meta:
                data = param_meta[param.name]
                param_info.doc = data.desc.splitlines()
                param_info.ptyp = data.ptyp
            
            param_cxt = param_info.cxt()
            _parameters.update(param_cxt)
        
        _returns = {}
        return_meta = self.document.get('return', None)
        if return_meta:
            data = [*return_meta.values()][0]
            doc = data.desc.splitlines()
            ptyp = data.ptyp
            _returns = dict(doc=doc, ptyp=ptyp)
        
        self.parameters = _parameters
        self.returns = _returns
        self.properties = dict(parameters=self.parameters, returns=self.returns)


class ParamInfo(Member):
    def __init__(self, param: Parameter):
        super().__init__(param, param.name)
        self.ptyp = ''
        self.param_kind = param.kind
        self.has_default = param.default is not Parameter.empty
        self.default = param.default if self.has_default else None
        self._variadic = self.param_kind in [2, 4]
        self.required = not self._variadic and not self.has_default
    
    def cxt(self):
        kind = self.param_kind.name.lower()
        ptyp = self.ptyp.replace('Optional', '').strip('[]')
        cxt = dict(kind=kind, ptyp=ptyp,
                   default=self.default, has_default=self.has_default,
                   required=self.required, doc=self.doc)
        return {self.name: cxt}


def _module_info(module):
    # Returns member info for an imported python module.
    
    # Multilevel nested dictionary:
    #   - module
    #   -- classes
    #   --- attributes
    #   ----- properties
    
    mem = Member(module)
    classes = {}
    for cls in mem.get_members(isclass):
        if cls.name.startswith('_'):
            continue
        cls_info = _class_info(cls)
        classes.update({cls.name: cls_info})
    
    mod_info = dict(classes=classes)
    return mod_info


def _info(obj):
    if not isinstance(obj, Member):
        obj = Member(obj)
    attributes = OrderedDict()
    clss = obj.get_classes()
    data = obj.get_data()
    prop = obj.get_properties()
    func = obj.get_methods()
    if clss:
        attributes['classes'] = {x.name: _info(x) for x in clss}
    if data:
        attributes['data'] = {x.name: x.cxt() for x in data}
    if prop:
        attributes['properties'] = {x.name: x.cxt() for x in prop}
    if func:
        attributes['functions'] = {x.name: x.cxt() for x in func}
    if obj.doc:
        attributes['doc'] = obj.doc
    return attributes


def _class_info(obj):
    if isclass(obj):
        obj = Member(obj)
    if not isclass(obj.typ):
        return
    attributes = OrderedDict()
    data = {x.name: x.cxt() for x in obj.get_data()}
    prop = {x.name: x.cxt() for x in obj.get_properties()}
    func = {x.name: x.cxt() for x in obj.get_methods()}
    if data:
        attributes['data'] = data
    if prop:
        attributes['prop'] = prop
    if func:
        attributes['func'] = func
    cls_attr = dict(attributes=attributes, doc=obj.doc)
    return cls_attr


# def _base_module_attrs(module):
#     """Classify public module attributes,
#     return as (name, category, value) tuples sorted by name."""
#
#     if not ismodule(module):
#         raise TypeError("module must be of <class 'module'>")
#
#     base = [Member(m[1], m[0]) for m in getmembers(module) if _is_pub(m[0]) and not isclass(m[1])]
#
#     if base:
#         data = {}
#         func = {}
#         attr = OrderedDict()
#
#         for b in base:
#             if isroutine(b.obj):
#                 at = (Attribute(b.name, 'mod func', module, b.obj))
#                 fi = FuncInfo(at)
#                 func[b.name] = fi.cxt()
#             else:
#                 at = (Attribute(b.name, 'mod data', module, b.obj))
#                 di = DataInfo(at)
#                 data[b.name] = di.cxt()
#
#         if data:
#             attr['data'] = data
#         if func:
#             attr['functions'] = func
#
#     return attr


def _obj_doc(obj):
    _doc = getdoc(obj)
    return _doc.splitlines() if isinstance(_doc, str) else ''


def _obj_mod(obj):
    mod = getmodule(obj)
    if ismodule(mod):
        pkg = mod.__package__
        base = sys.modules.get(pkg, None)
        return base


def _obj_name(obj):
    for i in range(0, 4):
        if i == 0:
            pass
        elif i == 1:
            if hasattr(obj, '__func__'):
                obj = obj.__func__
        elif i == 2:
            if isinstance(obj, property):
                obj = obj.fget
        elif i == 3:
            obj = type(obj)
        if hasattr(obj, '__name__'):
            return obj.__name__


def _obj_cls(obj):
    if isbuiltin(obj):
        return obj.__class__
    if _is_prop(obj):
        cls = _obj_qual(obj.fget)
        if cls:
            return cls
    if _is_bound(obj):
        cls = _obj_qual(obj.__func__)
        if cls:
            return cls
    if ismethod(obj):
        for cls in getmro(obj.__self__.__class__):
            if cls.__dict__.get(obj.__name__) is obj:
                return cls
        obj = obj.__func__  # fallback to __qualname__ parsing
    cls = _obj_qual(obj)
    if cls:
        return cls
    return getattr(obj, '__objclass__', None)  # handle special descriptor objects


def _obj_qual(obj):
    if isfunction(obj):
        cls = getattr(getmodule(obj),
                      obj.__qualname__.split('.<locals>', 1)[0].rsplit('.', 1)[0])
        if isinstance(cls, type):
            return cls


def _obj_group(obj):
    if ismodule(obj):
        return MemberGroup.MODULE
    elif isclass(obj) or hasattr(obj, '__slots__'):
        return MemberGroup.CLASS
    elif isroutine(obj):
        return MemberGroup.FUNCTION
    elif _is_primitive(obj):
        return MemberGroup.DATA
    return MemberGroup.UNDEF


def _cls_from_str(module_str, class_str):
    # load the module, will raise ImportError if module cannot be loaded
    m = __import__(module_str, globals(), locals(), class_str)
    # get the class, will raise AttributeError if class cannot be found
    c = getattr(m, class_str)
    return c


def _obj_out(obj):
    name = _obj_name(obj)
    return name, obj


def _is_bound(obj):
    _self = getattr(obj, '__self__', None)
    return _self is not None


def _is_prop(obj):
    return isinstance(obj, property)


def _is_pub(name):
    return not name.startswith('_') or name is '__init__'


def _is_primitive(obj):
    if hasattr(obj, '__slots__'):
        return False
    if hasattr(obj, '__class__'):
        if hasattr(obj.__class__, '__module__'):
            if not obj.__class__.__module__ == 'builtins':
                return False
    return not hasattr(obj, '__dict__')


def _doc_meta(obj):
    meta = {'params': {}, 'return': {}}
    try:
        src = getsource(obj)
    except (TypeError, OSError):
        return meta
    
    stream = io.StringIO(src)
    
    sys.stdin = stream
    pyc = pyment.PyComment('-')
    pyc.docs_init_to_class()
    sys.stdin = sys.__stdin__
    
    doc_list = pyc.docs_list[0]['docs']
    doc_index = doc_list.docs['in']
    
    for mk in meta.keys():
        item = doc_index[mk]
        if item:
            data = {i[0]: Element(*i) for i in item}
            meta[mk] = data
    
    return meta
