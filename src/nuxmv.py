# TODO: IMPLEMENT THIS
import re


# type specifiers -------------------------

class XMVType():
    pass

class XMVNoType(XMVType):
    pass


class XMVBoolean(XMVType):
    def __repr__(self) -> str:
        return "boolean"
    
class XMVInteger(XMVType):
    def __repr__(self) -> str:
        return "integer"
    
class XMVReal(XMVType):
    def __repr__(self) -> str:
        return "real"
    
class XMVClock(XMVType):
    def __repr__(self) -> str:
        return "clock"

class XMVWord(XMVType):
    def __init__(self, width: int, signed: bool):
        self.width = width
        self.signed = signed

    def __repr__(self) -> str:
        if self.signed:
            return f"signed word[{self.width}]"
        else:
            return f"unsigned word[{self.width}]"

class XMVEnumeration(XMVType):
    def __init__(self, summands: list[str]):
        self.summands = summands

    def __repr__(self) -> str:
        return f"enum({self.summands})"

class XMVRange(XMVType):
    def __init__(self, low: int, high: int):
        self.low = low
        self.high = high

    def __repr__(self) -> str:
        return f"{self.low} .. {self.high}"
    
class XMVArray(XMVType):
    def __init__(self, low: int, high: int, type: XMVType):
        self.low = low
        self.high = high
        self.type = type

    def __repr__(self) -> str:
        return f"array {self.low} .. {self.high} of {self.type}"
    
class XMVModuleType(XMVType):
    def __init__(self, module_name: str, parameters: list[str]):
        self.module_name = module_name
        self.parameters = parameters

    def __repr__(self) -> str:
        return f"{self.module_name}({self.parameters})"
    
# type specifiers -------------------------

class XMVLTLExpr():
    pass

class XMVLTLLogBinop(XMVLTLExpr):
    def __init__(self, op: str, lhs: XMVLTLExpr, rhs: XMVLTLExpr):
        self.op = op
        self.lhs = lhs
        self.rhs = rhs

    def __repr__(self) -> str:
        return f"{self.lhs} {self.op} {self.rhs}"
    
class XMVLTLLogUnop(XMVLTLExpr):
    def __init__(self, op: str, arg: XMVLTLExpr):
        self.op = op
        self.arg = arg

    def __repr__(self) -> str:
        return f"{self.op} {self.arg}"
    
class XMVLTLUnop(XMVLTLExpr):
    def __init__(self, op: str, arg: XMVLTLExpr):
        self.op = op
        self.arg = arg

    def __repr__(self) -> str:
        return f"{self.op} {self.arg}"
    
class XMVLTLBinop(XMVLTLExpr):
    def __init__(self, op: str, lhs: XMVLTLExpr, rhs: XMVLTLExpr):
        self.op = op
        self.lhs = lhs
        self.rhs = rhs

    def __repr__(self) -> str:
        return f"{self.lhs} {self.op} {self.rhs}"




class XMVExpr():
    
    def __init__(self) -> None:
        self.type = XMVNoType()
            

class XMVComplexIdentifier(XMVExpr):
    pass

class XMVConstant(XMVExpr):
    pass

class XMVIntegerConstant(XMVConstant):
    def __init__(self, integer: int):
        self.integer = integer

    def __repr__(self) -> str:
        return f"{self.integer}"
    
class XMVBooleanConstant(XMVConstant):
    def __init__(self, boolean: bool):
        self.boolean = boolean

    def __repr__(self) -> str:
        return f"{self.boolean}"
    
class XMVSymbolicConstant(XMVConstant):
    def __init__(self, symbol: XMVComplexIdentifier):
        self.symbol = symbol

    def __repr__(self) -> str:
        return f"{self.symbol}"
    
class XMVWordConstant(XMVConstant):
    def __init__(self, wconstant: str):
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
            self.width = numbers_pre_underscore[0]

        post_underscore: str = spl[1]

        self.value = post_underscore

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
        self.low = low
        self.high = high
    
    def __repr__(self) -> str:
        return f"{self.low} .. {self.high}"

class XMVFuncall(XMVExpr):
    def __init__(self, function_name: str, function_args: list[XMVExpr]):
        self.function_name = function_name
        self.function_args = function_args

    def __repr__(self) -> str:
        return f"{self.function_name}({self.function_args})"

class XMVBinop(XMVExpr):
    def __init__(self, op: str, lhs: XMVExpr, rhs: XMVExpr):
        self.op = op
        self.lhs = lhs
        self.rhs = rhs

    def __repr__(self) -> str:
        return f"{self.lhs} {self.op} {self.rhs}"

class XMVUnop(XMVExpr):
    def __init__(self, op: str, arg: XMVExpr):
        self.op = op
        self.arg = arg

    def __repr__(self) -> str:
        return f"{self.op}{self.arg}"
    
class XMVIndexSubscript(XMVExpr):
    def __init__(self, array: XMVExpr, index: int):
        self.array = array
        self.index = index

    def __repr__(self) -> str:
        return f"{self.array}[{self.index}]"

class XMVWordBitSelection(XMVExpr):
    def __init__(self, word: XMVExpr, low: int, high: int):
        self.word = word
        self.low = low
        self.high = high

    def __repr__(self) -> str:
        return f"{self.word}[{self.low} : {self.high}]"

class XMVSetBodyExpression(XMVExpr):
    def __init__(self, members: list[XMVExpr]):
        self.members = members

    def __repr__(self) -> str:
        return f"set({self.members})"

class XMVTernary(XMVExpr):
    def __init__(self, cond: XMVExpr, then_expr: XMVExpr, else_expr: XMVExpr):
        self.cond = cond
        self.then_expr = then_expr
        self.else_expr = else_expr

    def __repr__(self) -> str:
        return f"{self.cond} ? {self.then_expr} : {self.else_expr}"
    

class XMVCaseExpr(XMVExpr):
    def __init__(self, branches: list[tuple[XMVExpr, XMVExpr]]):
        self.branches = branches

    def __repr__(self) -> str:
        branches = "\n".join(f"{cond} : {branch}" for (cond, branch) in self.branches)
        return f"case {branches} esac ;"

class XMVIdentifier(XMVComplexIdentifier):
    def __init__(self, ident: str):
        self.ident = ident

    def __repr__(self) -> str:
        return f"{self.ident}"


class XMVModuleAccess(XMVComplexIdentifier):
    def __init__(self, module: XMVComplexIdentifier, element: XMVIdentifier):
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
    
class XMVLtlspecDeclaration(XMVModuleElement):
    def __init__(self, formula: XMVLTLExpr):
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


class XMVSpecification():
    def __init__(self, modules: list[XMVModule]):
        self.modules: list[XMVModule] = modules

    def __repr__(self) -> str:
        return "\n".join(str(mod) for mod in self.modules)
    

def type_check(spec: XMVSpecification) -> bool:

    def type_check_expr(expr: XMVExpr) -> bool:
        return True

    return True


