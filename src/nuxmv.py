# TODO: IMPLEMENT THIS
import re


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
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, XMVInteger)

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

    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, XMVEnumeration)

    def __repr__(self) -> str:
        return f"enum({self.summands})"

# class XMVRange(XMVType):
#     def __init__(self, low: int, high: int):
#         self.low = low
#         self.high = high

#     def __repr__(self) -> str:
#         return f"{self.low} .. {self.high}"
    
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
        self.type: XMVType = XMVNoType()
            

class XMVComplexIdentifier(XMVExpr):
    def __init__(self) -> None:
        super().__init__()

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
        return f"{self.name}({self.args})"

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
    def __init__(self, array: XMVExpr, index: int):
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
        super().__init__()
        self.ident = ident

    def __repr__(self) -> str:
        return f"{self.ident}"
    
class XMVSymbolicConstant(XMVConstant):
    def __init__(self, symbol: XMVIdentifier):
        super().__init__()
        self.symbol = symbol
        self.type = XMVEnumeration({symbol.ident})

    def __repr__(self) -> str:
        return f"{self.symbol}"


class XMVModuleAccess(XMVComplexIdentifier):
    def __init__(self, module: XMVComplexIdentifier, element: XMVIdentifier):
        super().__init__()
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
    
class XMVContext():

    def __init__(self) -> None:
        self.vars: dict[str, XMVType] = {}
        self.frozen_vars: set[str] = set()
        self.defs: dict[str, XMVExpr] = {}
        self.init: list[XMVExpr] = []
        self.invar: list[XMVExpr] = []
        self.trans: list[XMVExpr] = []
        self.invarspecs: list[XMVExpr] = []


def type_check(module: XMVModule) -> tuple[bool, XMVContext]:
    context = XMVContext()

    def propagate_next(expr: XMVExpr):
        # complex next expressions must propagate the next, for example:
        #    next((1 + a) + b) becomes (1 + next(a)) + next(b)
        # we also check for nested nexts here, for example:
        #    next(next(a)) is not allowed
        pass

    def type_check_expr(expr: XMVExpr, context: XMVContext) -> bool:
        # see starting on p16 of nuxmv user manual
        match expr:
            case XMVIntegerConstant(integer=i):
                pass
            case XMVBooleanConstant(boolean=b):
                pass
            case XMVSymbolicConstant(symbol=s):
                pass
            case XMVWordConstant(width=w, value=v):
                pass
            case XMVRangeConstant():
                pass
            case XMVFunCall(name="next", args=args):
                if len(args) != 1:
                    raise ValueError(f"`next` expr only allowed on operand {expr}")

                arg = args[0]
                type_check_expr(arg, context)

                expr.type = arg.type
            case XMVFunCall(name="signed", args=args):
                if len(args) != 1:
                    raise ValueError(f"`signed` expr only allowed on operand {expr}")

                arg: XMVExpr = args[0]
                type_check_expr(arg, context)

                if not isinstance(arg.type, XMVWord):
                    raise ValueError(f"Invalid argument for 'signed' {arg}, {expr}")

                expr.type = XMVWord(width=arg.type.width, signed=True)
            case XMVFunCall(name="unsigned", args=args):
                if len(args) != 1:
                    raise ValueError(f"`unsigned` expr only allowed on operand {expr}")

                arg: XMVExpr = args[0]
                type_check_expr(arg, context)

                if not isinstance(arg.type, XMVWord):
                    raise ValueError(f"Invalid argument for 'signed' {arg}, {expr}")

                expr.type = XMVWord(width=arg.type.width, signed=False)
            case XMVUnOp(op=op, arg=arg):
                type_check_expr(arg, context)

                if isinstance(arg.type, (XMVReal, XMVClock)):
                    raise ValueError(f"Unsupported type for {arg}, {arg.type}")

                match (op, arg.type):
                    case ("!", XMVBoolean()) | ("!", XMVWord()):
                        expr.type = arg.type
                    case ("-", XMVBoolean()) | ("-", XMVWord()) | ("-", XMVInteger()):
                        expr.type = arg.type
                    case _:
                        raise ValueError(f"Type checking error for {op}")
            case XMVBinOp(op=op, lhs=lhs, rhs=rhs):
                type_check_expr(lhs, context)
                type_check_expr(rhs, context)

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
                            case (XMVInteger(), XMVInteger()):
                                expr.type = XMVBoolean()
                            case (XMVWord(width=w1, signed=s1), XMVWord(width=w2, signed=s2)):
                                if w1 != w2 or s1 != s2:
                                    raise ValueError(f"Words not of same width and sign {expr}, {lhs.type} {rhs.type}")
                                expr.type = XMVBoolean()
                            case (XMVEnumeration(), XMVEnumeration()):
                                pass
                            case _:
                                raise ValueError(f"Type check error for {expr} ({lhs.type}, {rhs.type})")
                    case "+" | "-" | "*" | "/" | "%":
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
                        raise ValueError(f"Unsupported op {op}, {expr}")
            case XMVIndexSubscript():
                pass
            case XMVWordBitSelection(word=word, low=low, high=high):
                pass
            case XMVSetBodyExpression():
                pass
            case XMVTernary():
                pass
            case XMVCaseExpr(branches=branches):
                for (cond, branch) in branches:
                    type_check_expr(cond, context)
                    if (not isinstance(cond.type, XMVBoolean) and 
                        not (isinstance(cond.type, XMVWord) and cond.type.width == 1)):
                        raise ValueError(f"Case condition must be Boolean {expr}, {cond}")
                    
                    type_check_expr(branch, context)
                    # TODO: check that branches all have same type
                    expr.type = branch.type
            case XMVIdentifier(ident=ident):
                if ident in context.vars:
                    expr.type = context.vars[ident]
                elif ident in context.defs:
                    expr.type = context.defs[ident].type
                else:
                    raise ValueError(f"Variable {expr} not declared")
            case XMVModuleAccess():
                pass
            case _:
                pass

        return True

    # forward references are allowed....ugh
    for element in module.elements:
        match element:
            case XMVVarDeclaration(var_list=var_list, modifier=modifier):
                for (xmv_id, xmv_type) in var_list:
                    context.vars[xmv_id.ident] = xmv_type
                    if modifier == "FROZENVAR":
                        context.frozen_vars.add(xmv_id)
            case _:
                pass

    for element in module.elements:
        match element:
            case XMVDefineDeclaration(define_list=define_list):
                for define in define_list:
                    type_check_expr(define.expr, context)
                    context.defs[define.name.ident] = define.expr
            case _:
                pass

    for element in module.elements:
        match element:
            case XMVAssignDeclaration(assign_list=assign_list):
                raise ValueError(f"Unsupported element ASSIGN")
            case XMVTransDeclaration(formula=formula):
                type_check_expr(formula, context)
                context.trans.append(formula)
            case XMVInitDeclaration(formula=formula):
                type_check_expr(formula, context)
                context.init.append(formula)
            case XMVInvarDeclaration(formula=formula):
                type_check_expr(formula, context)
                context.invar.append(formula)
            case XMVInvarspecDeclaration(formula=formula):
                type_check_expr(formula, context)
                context.invarspecs.append(formula)
            case XMVLTLSpecDeclaration(formula=formula):
                raise ValueError(f"Unsupported element LTLSPEC")
            case _:
                pass

    return (True, context)


