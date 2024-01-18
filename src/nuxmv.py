# TODO: IMPLEMENT THIS
from __future__ import annotations
from operator import is_
from typing import Optional, cast

import re

from .util import logger
from .mcil import MCILVar, MCILSort

symbol_counter = 0
def fresh_symbol(st: str):
    global symbol_counter
    symbol_counter += 1
    return st + str(symbol_counter)


# forward declaration of XMVExpr

# class XMVExpr():
#     pass

# type specifiers -------------------------

class XMVType():
    pass

class XMVNoType(XMVType):
    pass


class XMVBoolean(XMVType):
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, XMVBoolean)

    def __repr__(self) -> str:
        return "boolean"
    
class XMVInteger(XMVType):
    def __init__(self, values: Optional[set[int]] = None) -> None:
        super().__init__()
        self.values = values

    def __eq__(self, __o: object) -> bool:
        return (isinstance(__o, XMVInteger) 
                or (isinstance(__o, XMVEnumeration) and __o.is_integer()))

    def __repr__(self) -> str:
        return "integer"
    
class XMVReal(XMVType):
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, XMVReal)

    def __repr__(self) -> str:
        return "real"
    
class XMVClock(XMVType):
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, XMVClock)

    def __repr__(self) -> str:
        return "clock"

class XMVWord(XMVType):
    def __init__(self, width: int, signed: bool):
        self.width = width
        self.signed = signed

    def __eq__(self, __o: object) -> bool:
        return (isinstance(__o, XMVWord) and 
                __o.width == self.width and
                __o.signed == self.signed)

    def __repr__(self) -> str:
        if self.signed:
            return f"signed word[{self.width}]"
        else:
            return f"unsigned word[{self.width}]"

class XMVEnumeration(XMVType):
    # enum types can overlap, so this is valid:
    # t1: {e1, e2, e3};
    # t2: {e4, e5, e3};
    # t1 = e3;
    # t1 = t2; -- now t1 = t3 = e3 
    def __init__(self, summands: set[str|int]):
        self.summands = summands

    def is_integer(self) -> bool:
        """Returns true if every summand of this type is an integer."""
        return all([isinstance(s, int) for s in self.summands])

    def is_symbolic(self) -> bool:
        """Returns true if every summand of this type is a str."""
        return all([isinstance(s, str) for s in self.summands])

    def is_integers_and_symbolic(self) -> bool:
        """Returns true if there is at least one summand of an integer type and one of a str type."""
        return (any([isinstance(s, int) for s in self.summands])
                and any([isinstance(s, str) for s in self.summands]))

    def __eq__(self, __o: object) -> bool:
        return (isinstance(__o, XMVEnumeration) 
                or (self.is_integer() and isinstance(__o, XMVInteger)))

    def __repr__(self) -> str:
        return f"enum({self.summands})"

class XMVArray(XMVType):
    def __init__(self, low: int, high: int, subtype: XMVType):
        self.low = low
        self.high = high
        self.subtype = subtype

    def __eq__(self, __o: object) -> bool:
        return (isinstance(__o, XMVArray) and
                 __o.low == self.low and 
                 __o.high == self.high and 
                 __o.subtype == self.subtype)

    def __repr__(self) -> str:
        return f"array {self.low} .. {self.high} of {self.subtype}"

class XMVWordArray(XMVType):
    def __init__(self, word_length: int, subtype: XMVType):
        self.word_length = word_length
        self.subtype = subtype

    def __eq__(self, __o: object) -> bool:
        return (isinstance(__o, XMVWordArray) and
                 __o.word_length == self.word_length and
                 __o.subtype == self.subtype)

    def __repr__(self) -> str:
        return f"array word[{self.word_length}] of {self.subtype}"    

class XMVModuleType(XMVType):
    def __init__(self, module_name: str, parameters: list[XMVExpr]):
        self.module_name = module_name
        self.parameters = parameters

    def __repr__(self) -> str:
        return f"{self.module_name}({self.parameters})"
    
def is_integer_type(xmv_type: XMVType) -> bool:
    return (isinstance(xmv_type, XMVInteger) 
            or (isinstance(xmv_type, XMVEnumeration) and xmv_type.is_integer()))
    
# type specifiers -------------------------

class XMVExpr():
    def __init__(self) -> None:
        self.type: XMVType = XMVNoType()

    def __hash__(self) -> int:
        return hash(repr(self))
            
class XMVComplexIdentifier(XMVExpr):
    def __init__(self, ident: str) -> None:
        super().__init__()
        self.ident = ident

class XMVConstant(XMVExpr):
    def __init__(self) -> None:
        super().__init__()

class XMVIntegerConstant(XMVConstant):
    def __init__(self, integer: int):
        super().__init__()
        self.integer = integer
        self.type = XMVInteger()

    def __repr__(self) -> str:
        return f"{self.integer}"
    
class XMVBooleanConstant(XMVConstant):
    def __init__(self, boolean: bool):
        super().__init__()
        self.boolean = boolean
        self.type = XMVBoolean()

    def __repr__(self) -> str:
        return f"{self.boolean}"
    
class XMVWordConstant(XMVConstant):
    def __init__(self, wconstant: str):
        super().__init__()

        if wconstant.find("s") != -1:
            self.signed = True
        else:
            self.signed = False

        if wconstant.find("b") != -1 or wconstant.find("B") != -1:
            self.base = "binary"

        if wconstant.find("o") != -1 or wconstant.find("O") != -1:
            self.base = "octal"

        if wconstant.find("d") != -1 or wconstant.find("D") != -1:
            self.base = "decimal"

        if wconstant.find("h") != -1 or wconstant.find("H") != -1:
            self.base = "hexadecimal"

        spl = wconstant.split("_")
        pre_underscore: str = spl[0][1:] # stripping off the starting 0

        numbers_pre_underscore = re.findall(r'\d+', pre_underscore)
        if numbers_pre_underscore != []:
            self.width = int(numbers_pre_underscore[0])

        post_underscore: str = spl[1]

        self.value = post_underscore

        self.type = XMVWord(self.width, self.signed)

    def __repr__(self) -> str:
        if self.signed:
            signed = "s"
        else:
            signed = "u"

        match self.base:
            case "binary":
                base = "b"
            case "octal":
                base = "o"
            case "decimal":
                base = "d"
            case "hexadecimal":
                base = "h"
            case _:
                raise ValueError(f"Invalid base! {self.base}")

        
        return f"0{signed}{base}{self.width}_{self.value}"

class XMVRangeConstant(XMVConstant):
    def __init__(self, low: int, high: int):
        super().__init__()
        self.low = low
        self.high = high
        self.type = XMVEnumeration(set(range(low,high+1)))
    
    def __repr__(self) -> str:
        return f"{self.low} .. {self.high}"

class XMVFunCall(XMVExpr):
    def __init__(self, name: str, args: list[XMVExpr]):
        super().__init__()
        self.name = name
        self.args = args

    def __repr__(self) -> str:
        return f"{self.name}({', '.join(str(a) for a in self.args)})"

class XMVBinOp(XMVExpr):
    def __init__(self, op: str, lhs: XMVExpr, rhs: XMVExpr):
        super().__init__()
        self.op = op
        self.lhs = lhs
        self.rhs = rhs

    def __repr__(self) -> str:
        return f"{self.lhs} {self.op} {self.rhs}"

class XMVUnOp(XMVExpr):
    def __init__(self, op: str, arg: XMVExpr):
        super().__init__()
        self.op = op
        self.arg = arg

    def __repr__(self) -> str:
        return f"{self.op}{self.arg}"
    
class XMVIndexSubscript(XMVExpr):
    def __init__(self, array: XMVExpr, index: XMVExpr):
        super().__init__()
        self.array = array
        self.index = index

    def __repr__(self) -> str:
        return f"{self.array}[{self.index}]"

class XMVWordBitSelection(XMVExpr):
    def __init__(self, word: XMVExpr, low: int, high: int):
        super().__init__()
        self.word = word
        self.low = low
        self.high = high

        # slices are always unsigned, see p19 of nuxmv user manual
        self.type = XMVWord(high-low+1, False) 

    def __repr__(self) -> str:
        return f"{self.word}[{self.low} : {self.high}]"

class XMVSetBodyExpression(XMVExpr):
    def __init__(self, members: list[XMVExpr]):
        super().__init__()
        self.members = members

    def __repr__(self) -> str:
        return f"set({self.members})"

class XMVTernary(XMVExpr):
    def __init__(self, cond: XMVExpr, then_expr: XMVExpr, else_expr: XMVExpr):
        super().__init__()
        self.cond = cond
        self.then_expr = then_expr
        self.else_expr = else_expr

    def __repr__(self) -> str:
        return f"{self.cond} ? {self.then_expr} : {self.else_expr}"
    

class XMVCaseExpr(XMVExpr):
    def __init__(self, branches: list[tuple[XMVExpr, XMVExpr]]):
        super().__init__()
        self.branches = branches

    def __repr__(self) -> str:
        branches = "\n".join(f"{cond} : {branch}" for (cond, branch) in self.branches)
        return f"case {branches} esac ;"

class XMVIdentifier(XMVComplexIdentifier):
    def __init__(self, ident: str):
        super().__init__(ident)

    def __repr__(self) -> str:
        return f"{self.ident}"

    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, XMVIdentifier) and __o.ident == self.ident

    def __hash__(self) -> int:
        return hash(self.ident)
    
class XMVSymbolicConstant(XMVConstant):
    def __init__(self, symbol: XMVComplexIdentifier):
        super().__init__()
        self.symbol = symbol

    def __repr__(self) -> str:
        return f"{self.symbol}"


class XMVModuleAccess(XMVComplexIdentifier):
    def __init__(self, module: XMVComplexIdentifier, element: XMVIdentifier):
        super().__init__(module.ident)
        self.module = module
        self.element = element

    def __repr__(self) -> str:
        return f"{self.module} . {self.element}"

# class XMVArrayAccess(XMVComplexIdentifier):
#     def __init__(self, array: XMVArray, index):
#         self.array = array
#         self.index = index

#     def __repr__(self) -> str:
#         return f"{self.array}[{self.index}]"

# module elements -------------------------

# Module elements
class XMVModuleElement():
    pass

class XMVVarDeclaration(XMVModuleElement):
    def __init__(
            self, 
            var_list: list[tuple[XMVIdentifier, XMVType]],
            modifier: str
    ):
        self.var_list = var_list
        match modifier:
            case "VAR":
                self.modifier = "VAR"
            case "IVAR":
                self.modifier = "IVAR"
            case "FROZENVAR":
                self.modifier = "FROZENVAR"
            case _:
                raise ValueError(f"Invalid VAR modifier: {modifier} -- must be either `VAR`/`IVAR`/`FROZENVAR`")

    def __repr__(self) -> str:
        def var_str(var: str, type: XMVType) -> str:
            return f"{var} : {type}"
        var_list_str = "\n".join(var_str(var[0].ident, var[1]) for var in self.var_list)
        return f"{self.modifier}\n" + var_list_str
    
class XMVFunction():
    def __init__(self, name: str, type: tuple[list[XMVType], XMVType]):
        self.name = name
        self.type = type
    
    def __repr__(self) -> str:
        domain = self.type[0]
        function_domain_str: str = str(domain[0])
        for d in domain[1:]:
            function_domain_str += "*" + str(d)
        function_type_str = f"{function_domain_str} -> {self.type[1]}"
        return f"{self.name} : {function_type_str}"

class XMVFunctionDeclaration(XMVModuleElement):
    def __init__(self, function_list: list[XMVFunction]):
        self.function_list = function_list
    
    def __repr__(self) -> str:
        return f"FUN {self.function_list}"
    

class XMVDefine():
    def __init__(self, name: XMVIdentifier, expr: XMVExpr):
        self.name = name
        self.expr = expr

    def __repr__(self) -> str:
        return f"{self.name} := {self.expr}"

class XMVDefineDeclaration(XMVModuleElement):
    def __init__(self, define_list: list[XMVDefine]):
        self.define_list = define_list

    def __repr__(self) -> str:
        return f"DEFINE {self.define_list}"
    
class XMVConstants():
    def __init__(self, identifier: XMVComplexIdentifier):
        self.identifier = identifier

    def __repr__(self) -> str:
        return f"{self.identifier}"

class XMVConstantsDeclaration(XMVModuleElement):
    def __init__(self, constants_list: list[XMVConstants]):
        self.constants_list = constants_list

    def __repr__(self) -> str:
        return f"CONSTANTS {self.constants_list}"
    
class XMVAssign():
    def __init__(self, lhs: XMVComplexIdentifier, rhs: XMVExpr, modifier: str):
        self.lhs = lhs
        self.rhs = rhs
        self.modifier = modifier

    def __repr__(self) -> str:
        match self.modifier:
            case "init":
                return f"init({self.lhs}) := {self.rhs}"
            case "next":
                return f"next({self.lhs}) := {self.rhs}"
            case "none":
                return f"{self.lhs} := {self.rhs}"
            case _:
                raise ValueError("Invalid XMVAssign modifier: {self.modifier} -- must be either `init`/`next`/`none`")

class XMVAssignDeclaration(XMVModuleElement):
    def __init__(self, assign_list: list[XMVAssign]):
        self.assign_list = assign_list

    def __repr__(self) -> str:
        return f"ASSIGN {self.assign_list}"

class XMVTransDeclaration(XMVModuleElement):
    def __init__(self, formula: XMVExpr):
        self.formula = formula

    def __repr__(self) -> str:
        return f"TRANS {self.formula}"
    
class XMVInitDeclaration(XMVModuleElement):
    def __init__(self, formula: XMVExpr):
        self.formula = formula

    def __repr__(self) -> str:
        return f"INIT {self.formula}"
    
class XMVInvarDeclaration(XMVModuleElement):
    def __init__(self, formula: XMVExpr):
        self.formula = formula

    def __repr__(self) -> str:
        return f"INVAR {self.formula}"
    
class XMVInvarspecDeclaration(XMVModuleElement):
    def __init__(self, formula: XMVExpr):
        self.formula = formula

    def __repr__(self) -> str:
        return f"INVARSPEC {self.formula}"
    
class XMVLTLSpecDeclaration(XMVModuleElement):
    def __init__(self, formula: XMVExpr):
        self.formula = formula

    def __repr__(self) -> str:
        return f"LTLSPEC {self.formula}"

# module elements -------------------------


# top level -------------------------

class XMVModule():
    def __init__(
            self, name: str,
            parameters: list[str],
            elements: list[XMVModuleElement]
    ):
        self.name = name
        self.parameters = parameters
        self.elements = elements

    def __repr__(self) -> str:
        bodies = "\n".join(str(elem) for elem in self.elements) + "\n"
        if self.parameters == []:
            return f"\nMODULE {self.name}\n" + bodies
        return f"\nMODULE {self.name} ({self.parameters})\n" + bodies


class XMVProgram():
    def __init__(self, modules: list[XMVModule], main: XMVModule):
        self.modules: list[XMVModule] = modules
        self.main: XMVModule = main

    def __repr__(self) -> str:
        return "\n".join(str(mod) for mod in self.modules)
    
class XMVContext():

    def __init__(self, modules: list[XMVModule]) -> None:
        # maps module name to all the variables it has, and then from those variables to their XMVTypes
        self.vars: dict[str, dict[str, XMVType]] = {m.name:{} for m in modules}
        self.frozen_vars: set[str] = set()
        self.defs: dict[str, dict[str, XMVExpr]] = {m.name:{} for m in modules}
        self.init: list[XMVExpr] = []
        self.invar: list[XMVExpr] = []
        self.trans: list[XMVExpr] = []
        self.invarspecs: list[XMVExpr] = []
        # enum1: {s1, s2, s3}; enum2: {t1, t2} --> [[s1, s2, s3], [t1, t2]] (assume they're unique) 
        self.enums: dict[str, XMVEnumeration] = {}
        # {s1 |-> enum1, s2 |-> enum1, s3 |-> enum1, t1 |-> enum2, t2 |-> enum2} (populated in translation)
        self.reverse_enums: dict[str, list[str]] = {}
        # maps {module_name |-> list of parameters (p1, t1), ...}, where pi is the variable and ti is its XMVType
        self.module_params: dict[str, dict[str, XMVType]] = {m.name:{} for m in modules}
        # maps {module_name |-> list of IL output variables} for use in submodule/local variable construction
        self.outputs: dict[str, list[tuple[str, MCILSort]]] = {}
        # maps {module_name |-> list of IL local variables} for use in submodule construction
        self.module_locals: dict[str, list[MCILVar]] = {}

        self.modules: dict[str, XMVModule] = {m.name:m for m in modules}
        self.module_dep_order: list[XMVModule] = []

        # maps {module_name |-> set of definition identifiers} for output variable construction
        self.referenced_defs: dict[str, set[str]] = {m.name:set() for m in modules}

        self.cur_module: Optional[XMVModule] = None

    def get_cur_module(self) -> XMVModule:
        if not self.cur_module:
            raise ValueError(f"cur_module not set in XMVContext")
        return self.cur_module
    
    def get_cur_defs(self) -> dict[str, XMVExpr]:
        return self.defs[self.get_cur_module().name]


# # precondition: context.parameters[pi] = ti
# def param_analysis(module: XMVModule, context: XMVContext) -> XMVContext:
#     mod_insts = [
#         vdecls
#         for elem in module.elements
#         if isinstance(elem, XMVVarDeclaration)
#         for vdecls in elem.var_list
#         if isinstance(vdecls[1], XMVModuleType)
#     ]
#     for mod_typ in [t for _,t in mod_insts if isinstance(t, XMVModuleType)]:
#         for i, param in enumerate(mod_typ.parameters):
#             type_check_expr(top_expr=param, context=context, cur_module=module)
#             param_ident = context.modules[mod_typ.module_name].parameters[i]
#             context.parameters[mod_typ.module_name][param_ident] = param.type
#         context = param_analysis(context.modules[mod_typ.module_name], context)
#     return context


# def top_down_param_analysis(spec: XMVProgram, context: XMVContext) -> XMVContext:
#     # logger.debug(f"initialized variables, context = {context.vars}")
#     # logger.debug(f"initialized parameters, context = {context.parameters}")
#     for module in spec.modules:
#         if module.name != "main":
#             continue
        
#         assert(module.name == "main")
#         new_context = param_analysis(module, context)
#         return context
    
#     raise ValueError("Module `main` not declared!")


# def type_check_enums(xmv_module: XMVModule, xmv_context: XMVContext) -> None:
#     for m in xmv_module.elements:
#         match m:
#             case XMVVarDeclaration():
#                 for (_, xmv_var_type) in m.var_list:
#                     match xmv_var_type:
#                         case XMVEnumeration(summands=summands):
#                             lsummands: list[str|int] = list(summands)
#                             xmv_context.enums.append(lsummands)
#                         case _:
#                             pass
#             case _:
#                 pass


def postorder_nuxmv(expr: XMVExpr, context: XMVContext):
    """Perform an iterative postorder traversal of 'expr'."""
    stack: list[tuple[bool, XMVExpr]] = []
    visited: set[int] = set()

    stack.append((False, expr))

    while len(stack) > 0:
        (seen, cur) = stack.pop()

        if seen:
            yield cur
            continue
        elif id(cur) in visited:
            continue

        visited.add(id(cur))
        stack.append((True, cur))
        
        match cur:
            case XMVIdentifier(ident=ident) if ident in context.get_cur_defs():
                stack.append((False, context.get_cur_defs()[ident]))
            case XMVFunCall(args=args):
                [stack.append((False, arg)) for arg in args]
            case XMVUnOp(arg=arg):
                stack.append((False, arg))
            case XMVBinOp(lhs=lhs, rhs=rhs):
                stack.append((False, lhs))
                stack.append((False, rhs))
            case XMVIndexSubscript(array=array, index=index):
                stack.append((False, array))
                stack.append((False, index))
            case XMVWordBitSelection(word=word, low=_, high=_):
                stack.append((False, word))
            case XMVSetBodyExpression(members=members):
                [stack.append((False, m)) for m in members]
            case XMVTernary(cond=cond, then_expr=then_expr, else_expr=else_expr):
                stack.append((False, cond))
                stack.append((False, then_expr))
                stack.append((False, else_expr))
            case XMVCaseExpr(branches=branches):
                for (cond, then_expr) in branches:
                    stack.append((False, cond))
                    stack.append((False, then_expr))
            case _:
                pass

def type_check_expr(top_expr: XMVExpr, context: XMVContext, cur_module: XMVModule) -> None:
    # see starting on p16 of nuxmv user manual
    # print(f"type_check_expr({expr})")

    for expr in postorder_nuxmv(top_expr, context):
        match expr:
            case XMVIntegerConstant():
                pass
            case XMVBooleanConstant():
                pass
            case XMVSymbolicConstant():
                pass
            case XMVWordConstant():
                pass
            case XMVRangeConstant():
                pass
            case XMVFunCall(name="next", args=args):
                if len(args) != 1:
                    raise ValueError(f"`next` expr only allowed one operand {expr}")

                expr.type = args[0].type
            case XMVFunCall(name="signed", args=args):
                if len(args) != 1:
                    raise ValueError(f"`signed` expr only allowed one operand {expr}")

                arg: XMVExpr = args[0]

                if not isinstance(arg.type, XMVWord):
                    raise ValueError(f"Invalid argument for 'signed' {arg}, {expr}")
                
                if arg.type.signed:
                    raise ValueError(f"Argument to `signed` must be unsigned word.")

                expr.type = XMVWord(width=arg.type.width, signed=True)
            case XMVFunCall(name="unsigned", args=args):
                if len(args) != 1:
                    raise ValueError(f"`unsigned` expr only allowed one operand {expr}")

                arg: XMVExpr = args[0]

                if not isinstance(arg.type, XMVWord):
                    raise ValueError(f"Invalid argument for 'signed' {arg}, {expr}")
                
                if not arg.type.signed:
                    raise ValueError(f"Argument to `signed` must be signed word.")

                expr.type = XMVWord(width=arg.type.width, signed=False)
            case XMVFunCall(name="READ", args=args):
                if len(args) != 2:
                    raise ValueError(f"'READ' expr must have 2 operands ({expr})")

                (arr, idx) = args

                match arr.type:
                    case XMVArray():
                        if not isinstance(idx.type, XMVInteger):
                            raise ValueError(f"'READ' expr index must be of integer type")
                    case XMVWordArray():
                        if not isinstance(idx.type, XMVWord):
                            raise ValueError(f"'READ' expr index must be of word type")
                    case _:
                        raise ValueError(f"'READ' expr must apply to array type, found {arr.type} ({expr})")

                expr.type = arr.type.subtype
            case XMVFunCall(name="WRITE", args=args):
                if len(args) != 3:
                    raise ValueError(f"'WRITE' expr must have 3 operands ({expr})")

                (arr, idx, val) = args

                match arr.type:
                    case XMVArray(subtype=subtype):
                        if not isinstance(idx.type, XMVInteger):
                            raise ValueError(f"'WRITE' expr index must be of integer type")
                    case XMVWordArray(subtype=subtype):
                        if not isinstance(idx.type, XMVWord):
                            raise ValueError(f"'WRITE' expr index must be of word type")
                    case _:
                        raise ValueError(f"'WRITE' expr must apply to array type, found {arr.type} ({expr})")

                if val.type != subtype:
                    raise ValueError(f"'WRITE' expr value must be same as array subtype, found {val.type}")

                expr.type = arr.type
            case XMVFunCall(name="typeof", args=args):
                if len(args) != 1:
                    raise ValueError(f"'typeof' operator only allowed one operand ({expr})")

                expr.type = args[0].type
            case XMVFunCall(name="CONSTARRAY", args=args):
                if len(args) != 2:
                    raise ValueError(f"")

                const_type, const_val = args

                if not isinstance(const_type, XMVFunCall) or const_type.name != "typeof":
                    raise ValueError(f"'CONSTARRAY' first operand must be 'typeof', found {const_type}")

                if not isinstance(const_type.type, (XMVArray, XMVWordArray)):
                    raise ValueError(f"'CONSTARRAY' first operand must be of array type, found {const_type.type}")

                if const_val.type != const_type.type.subtype:
                    raise ValueError(f"'CONSTARRAY' operands must match types {const_type.type}, {const_val.type}")
                    
                expr.type = const_type.type
            case XMVFunCall(name=name, args=args):
                raise NotImplementedError(f"Unsupported function {name}")
            case XMVUnOp(op=op, arg=arg):
                if isinstance(arg.type, (XMVReal, XMVClock)):
                    raise ValueError(f"Unsupported type for {arg}, {arg.type}")

                match (op, arg.type):
                    case ("!", XMVBoolean()) | ("!", XMVWord()):
                        expr.type = arg.type
                    case ("-", XMVBoolean()) | ("-", XMVWord()) | ("-", XMVInteger()):
                        expr.type = arg.type
                    case (("X", XMVBoolean()) | ("G", XMVBoolean()) | ("F", XMVBoolean()) | 
                          ("Y", XMVBoolean()) | ("H", XMVBoolean()) | ("O", XMVBoolean())
                    ):
                        expr.type = arg.type
                    case _:
                        raise ValueError(f"Type checking error for {op}: {arg.type}")
            case XMVBinOp(op=op, lhs=lhs, rhs=rhs):
                if isinstance(lhs.type, (XMVReal, XMVClock)):
                    raise ValueError(f"Unsupported type for {lhs}, {lhs.type}")
                elif isinstance(rhs.type, (XMVReal, XMVClock)):
                    raise ValueError(f"Unsupported type for {rhs}, {rhs.type}")
                    
                match op:
                    case "&" | "|" | "xor" | "xnor" | "->" | "<->":
                        match (lhs.type, rhs.type):
                            case (XMVBoolean(), XMVBoolean()):
                                expr.type = XMVBoolean()
                            case (XMVWord(width=w1, signed=s1), XMVWord(width=w2, signed=s2)):
                                if w1 != w2 or s1 != s2:
                                    raise ValueError(f"Words not of same width and sign {expr}, {lhs.type} {rhs.type}")
                                expr.type = XMVWord(w1,s1)
                            case _:
                                raise ValueError(f"Type checking error for {op} ({lhs.type}, {rhs.type})")
                    case "=" | "!=" | ">" | "<" | ">=" | "<=":
                        match (lhs.type, rhs.type):
                            case (XMVBoolean(), XMVBoolean()):
                                expr.type = XMVBoolean()
                            case (XMVInteger(), XMVInteger()):
                                expr.type = XMVBoolean()
                            case (XMVEnumeration(), XMVInteger()):
                                lhs_type = cast(XMVEnumeration, lhs.type)
                                if not lhs_type.is_integer():
                                    raise ValueError(f"Type check error for {expr} ({lhs.type}, {rhs.type})")
                                expr.type = XMVBoolean()
                            case (XMVInteger(), XMVEnumeration()):
                                rhs_type = cast(XMVEnumeration, rhs.type)
                                if not rhs_type.is_integer():
                                    raise ValueError(f"Type check error for {expr} ({lhs.type}, {rhs.type})")
                                expr.type = XMVBoolean()
                            case (XMVWord(width=w1, signed=s1), XMVWord(width=w2, signed=s2)):
                                if w1 != w2 or s1 != s2:
                                    raise ValueError(f"Words not of same width and sign {expr}, {lhs.type} {rhs.type}")
                                expr.type = XMVBoolean()
                            case (XMVArray(low=low1, high=high1, subtype=type1), 
                                  XMVArray(low=low2, high=high2, subtype=type2)):
                                if low1 != low2 and high1 != high2 and type1 != type2:
                                    raise ValueError("Different array types")
                                expr.type = XMVBoolean()
                            case (XMVWordArray(word_length=wl1, subtype=type1),
                                  XMVWordArray(word_length=wl2, subtype=type2)):
                                if wl1 != wl2 and type1 != type2:
                                    raise ValueError("Different word array types")
                                expr.type = XMVBoolean()
                            case (XMVEnumeration(), XMVEnumeration()):
                                lhs_type = cast(XMVEnumeration, lhs.type)
                                rhs_type = cast(XMVEnumeration, rhs.type)

                                if op == "=" or op == "!=":
                                    pass
                                elif not lhs_type.is_integer() or not rhs_type.is_integer():
                                    raise ValueError(f"Type check error for {expr} ({lhs.type}, {rhs.type})")

                                expr.type = XMVBoolean()
                            case _:
                                raise ValueError(f"Type check error for {expr} ({lhs.type}, {rhs.type})")
                    case "+" | "-" | "*" | "/" | "mod":
                        match (lhs.type, rhs.type):
                            case (XMVInteger(), XMVInteger()):
                                expr.type = XMVInteger()
                            case (XMVWord(width=w1, signed=s1), XMVWord(width=w2, signed=s2)):
                                if w1 != w2 or s1 != s2:
                                    raise ValueError(f"Words not of same width and sign {expr}, {lhs.type} {rhs.type}")
                                expr.type = XMVWord(w1,s1)
                            case _:
                                raise ValueError(f"Type check error for {expr} ({lhs.type}, {rhs.type})")
                    case "<<" | ">>":
                        match (lhs.type, rhs.type):
                            case (XMVWord(width=w, signed=s), XMVInteger()):
                                expr.type = XMVWord(width=w, signed=s)
                            case (XMVWord(width=w1, signed=s), XMVWord(width=w2, signed=False)):
                                expr.type = XMVWord(width=w1, signed=s)
                            case _:
                                raise ValueError(f"Type check error for {expr} ({lhs.type}, {rhs.type})")
                    case "concat":
                        match (lhs.type, rhs.type):
                            case (XMVWord(width=w1, signed=s1), XMVWord(width=w2, signed=s2)):
                                expr.type = XMVWord(width=w1+w2, signed=False)
                            case _:
                                raise ValueError(f"Type check error for {expr} ({lhs.type}, {rhs.type})")
                    case _:
                        raise ValueError(f"Unsupported op `{op}`, `{expr}`")
            case XMVIndexSubscript():
                raise NotImplementedError(f"Unsupported operator {type(expr)}")
            case XMVWordBitSelection(word=word, low=low, high=high):
                if not isinstance(word.type, XMVWord):
                    raise ValueError(f"Bit select only valid on words, found '{word.type}' ({expr})")

                if low < 0:
                    raise ValueError(f"Low value for bit select must be greater than 0 ({low})")

                if high >= word.type.width:
                    raise ValueError(f"High value for bit select must be less than word width, {high} >= {word.type.width} ({expr})")

                if low > high:
                    raise ValueError(f"High value for bit select must be greater than low value [{low}:{high}] ({expr})")
            case XMVSetBodyExpression():
                raise NotImplementedError(f"Unsupported operator {type(expr)}")
            case XMVTernary(cond=cond, then_expr=then_expr, else_expr=else_expr):
                if cond.type != XMVBoolean():
                    raise NotImplementedError(f"Condition of ternary must be boolean, found '{cond.type}'")

                if then_expr.type != else_expr.type:
                    raise NotImplementedError(f"Branches of ternary not the same."
                                            f"\n\tFound '{then_expr.type}' and '{else_expr.type}")
                
                expr.type = then_expr.type
            case XMVCaseExpr(branches=branches):
                for (cond, branch) in branches:
                    if (not isinstance(cond.type, XMVBoolean) and 
                        not (isinstance(cond.type, XMVWord) and cond.type.width == 1)):
                        raise ValueError(f"Case condition must be Boolean {expr}, {cond}")
                    
                    # TODO: check that branches all have same type
                    expr.type = branch.type
            case XMVIdentifier(ident=ident):
                # print(f"{context.module_params[cur_module.name]}, {expr.ident}")
                # print(expr.ident in context.module_params[cur_module.name])

                if ident in context.vars[cur_module.name]:
                    expr.type = context.vars[cur_module.name][ident]
                elif ident in context.defs[cur_module.name]:
                    expr.type = context.defs[cur_module.name][ident].type
                elif expr.ident in context.module_params[cur_module.name]:
                    expr.type = context.module_params[cur_module.name][expr.ident]
                else:
                    flag = False
                    for enum in context.enums.values():
                        if ident in enum.summands:
                            expr.type = XMVEnumeration(summands=set(enum.summands))
                            flag = True

                    if not flag:
                        raise ValueError(f"Variable {expr} not declared")

            case XMVModuleAccess(module=module, element=element):
                if isinstance(module, XMVModuleAccess):
                    id_w_elem: str = module.element.ident
                elif isinstance(module, XMVIdentifier):
                    id_w_elem: str = module.ident
                else:
                    raise ValueError(f"weird module access: {expr}")

                var_lists = [vd.var_list for vd in cur_module.elements if isinstance(vd, XMVVarDeclaration)]
                
                module_w_elem: str = ""
                for var_list in var_lists:
                    for (var_name, var_type) in var_list:
                        match var_type:
                            case XMVModuleType(module_name=found_name):
                                if var_name.ident == id_w_elem:
                                    module_w_elem = found_name
                            case _:
                                pass
                if (module_w_elem == ""):
                    raise ValueError(f"module {id_w_elem} not instantiated in current context")
                
                if element.ident in context.vars[module_w_elem]:
                    expr.type = context.vars[module_w_elem][element.ident]
                elif element.ident in context.module_params[module_w_elem]:
                    expr.type = context.module_params[module_w_elem][element.ident]
                elif element.ident in context.defs[module_w_elem]:
                    expr.type = context.defs[module_w_elem][element.ident].type
                    context.referenced_defs[module_w_elem].add(element.ident)
                else:
                    raise ValueError(f"{module}.{element}: {element} not a variable or parameter")
                # raise NotImplementedError(f"Unsupported operator {type(expr)}")
            case _:
                raise NotImplementedError(f"Unsupported operator {type(expr)} ({expr})")
            
        if (expr.type == XMVNoType()):
            raise ValueError(f"NOTYPE: {expr}")

def type_check_module(module: XMVModule, context: XMVContext) -> bool:
    logger.debug(f"Type checking module {module.name}")
    
    context.cur_module = module

    context.module_dep_order.append(module)

    context.vars[module.name] = {}
    context.defs[module.name] = {}

    # def propagate_next(expr: XMVExpr):
    #     # complex next expressions must propagate the next, for example:
    #     #    next((1 + a) + b) becomes (1 + next(a)) + next(b)
    #     # we also check for nested nexts here, for example:
    #     #    next(next(a)) is not allowed
    #     pass

    # Forward references are allowed....ugh
    # We go thru each element of the module and collect every declared symbol first --
    # then we type check each symbol later, traversing its expression/module tree as needed.
    for element in module.elements:
        match element:
            case XMVVarDeclaration(var_list=var_list, modifier=modifier):
                for (xmv_id, xmv_type) in var_list:
                    context.vars[module.name][xmv_id.ident] = xmv_type

                    if modifier == "FROZENVAR":
                        context.frozen_vars.add(xmv_id.ident)
                    
                    if isinstance(xmv_type, XMVEnumeration):
                        if xmv_type.is_integers_and_symbolic():
                            logger.error(f"integers-and-symbolic enums unsupported")
                            return False

                        new_sym: str = fresh_symbol("enum")
                        context.enums[new_sym] = xmv_type

                        set_list: list[str|int] = list(xmv_type.summands)
                        str_set_list: list[str] = [str(s) for s in set_list]

                        for st in str_set_list:
                            if st in context.reverse_enums:
                                context.reverse_enums[st].append(new_sym)
                            else:
                                context.reverse_enums[st] = [new_sym]
            case XMVDefineDeclaration(define_list=define_list):
                for define in define_list:
                    context.defs[module.name][define.name.ident] = define.expr
            case _:
                pass

    for var_decl in [vd for vd in module.elements if isinstance(vd, XMVVarDeclaration)]:
        for var_name,xmv_type in [
            (var_name,xmv_type) 
            for var_name,xmv_type 
            in var_decl.var_list 
            if isinstance(xmv_type, XMVModuleType)
        ]:
            signature: list[XMVType] = []

            for param in xmv_type.parameters:
                type_check_expr(top_expr=param, context=context, cur_module=module)
                signature.append(param.type)

            if xmv_type.module_name not in context.module_params:
                # first time instantiating this module type -- this is now the enforced signature
                target_module = context.modules[xmv_type.module_name]

                if len(target_module.parameters) != len(signature):
                    logger.error(f"Invalid number of parameters provided in module instantiation '{var_name}'." 
                                f"\n\tExpected {len(target_module.parameters)}, got {len(signature)}")
                    return False

                context.module_params[xmv_type.module_name] = {
                    param:xmv_type 
                    for param,xmv_type 
                    in zip(target_module.parameters, signature)
                }

                # we only type check modules if they are instantiated -- this is how nuXmv works too
                type_check_module(target_module, context)
                context.cur_module = module

                logger.debug(f"Done with module {module.name}")

                continue

            # maintain module dependency order
            target_module = context.modules[xmv_type.module_name]
            if target_module in context.module_dep_order:
                context.module_dep_order.remove(target_module)
                context.module_dep_order.append(target_module)

            module_signature = context.module_params[xmv_type.module_name].values()

            if len(signature) != len(module_signature):
                logger.error(f"Invalid number of parameters provided in module instantiation '{var_name}'." 
                            f"\n\tExpected {len(module_signature)}, got {len(signature)}")
                return False

            # MUST report if user is trying to dynamically type the module instantiations
            # since nuXmv won't yell at them for it and we don't support it
            for p1,p2 in zip(signature, module_signature):
                if p1 != p2:
                    logger.error(f"Parameter types for module instantiation disagree, modules must be statically typed."
                                f"\n\tExpected {' '.join(repr(module_signature))}"
                                f"\n\tGot {' '.join(repr(signature))}")
                    return False

    # Now type check each expression
    for element in module.elements:
        match element:
            case XMVDefineDeclaration(define_list=define_list):
                for define in define_list:
                    # TODO: is the check below helpful?
                    # if define.expr.type == XMVNoType():
                    logger.debug(f"Type checking DEFINE {define.name}")

                    type_check_expr(define.expr, context, module)
            case XMVAssignDeclaration(assign_list=assign_list):
                for assign in assign_list:
                    type_check_expr(assign.rhs, context, module)
            case XMVTransDeclaration(formula=formula):
                type_check_expr(formula, context, module)
                context.trans.append(formula)
            case XMVInitDeclaration(formula=formula):
                type_check_expr(formula, context, module)
                context.init.append(formula)
            case XMVInvarDeclaration(formula=formula):
                type_check_expr(formula, context, module)
                context.invar.append(formula)
            case XMVInvarspecDeclaration(formula=formula):
                type_check_expr(formula, context, module)
                context.invarspecs.append(formula)
            case XMVLTLSpecDeclaration(formula=formula):
                type_check_expr(formula, context, module)
            case _:
                pass

    return True


