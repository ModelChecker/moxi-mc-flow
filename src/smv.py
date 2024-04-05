from __future__ import annotations
from typing import Optional, cast
import pathlib
import re
import collections

from src import log, moxi

FILE_NAME = pathlib.Path(__file__).name

symbol_counter = 0


def fresh_symbol(st: str):
    global symbol_counter
    symbol_counter += 1
    return st + str(symbol_counter)


# type specifiers -------------------------


class Type:
    pass


class AnyType(Type):
    def __eq__(self, __value: object) -> bool:
        return isinstance(__value, AnyType)

    def __repr__(self) -> str:
        return "ANY"


class Boolean(Type):
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Boolean)

    def __repr__(self) -> str:
        return "boolean"


class Integer(Type):
    def __init__(self, values: Optional[set[int]] = None) -> None:
        super().__init__()
        self.values = values

    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Integer) or (
            isinstance(__o, Enumeration) and __o.is_integer()
        )

    def __repr__(self) -> str:
        return "integer"


class Real(Type):
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Real)

    def __repr__(self) -> str:
        return "real"


class Clock(Type):
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Clock)

    def __repr__(self) -> str:
        return "clock"


class Word(Type):
    def __init__(self, width: int, signed: bool):
        self.width = width
        self.signed = signed

    def __eq__(self, __o: object) -> bool:
        return (
            isinstance(__o, Word)
            and __o.width == self.width
            and __o.signed == self.signed
        )

    def __repr__(self) -> str:
        if self.signed:
            return f"signed word[{self.width}]"
        else:
            return f"unsigned word[{self.width}]"


class Enumeration(Type):
    # enum types can overlap, so this is valid:
    # t1: {e1, e2, e3};
    # t2: {e4, e5, e3};
    # t1 = e3;
    # t1 = t2; -- now t1 = t3 = e3
    def __init__(self, summands: set[str | int]):
        self.summands = summands

    def is_integer(self) -> bool:
        """Returns true if every summand of this type is an integer."""
        return all([isinstance(s, int) for s in self.summands])

    def is_symbolic(self) -> bool:
        """Returns true if every summand of this type is a str."""
        return all([isinstance(s, str) for s in self.summands])

    def is_integers_and_symbolic(self) -> bool:
        """Returns true if there is at least one summand of an integer type and one of a str type."""
        return any([isinstance(s, int) for s in self.summands]) and any(
            [isinstance(s, str) for s in self.summands]
        )

    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Enumeration) or (
            self.is_integer() and isinstance(__o, Integer)
        )

    def __repr__(self) -> str:
        return f"enum({','.join({str(s) for s in sorted(self.summands)})})"


class Array(Type):
    def __init__(self, low: int, high: int, subtype: Type):
        self.low = low
        self.high = high
        self.subtype = subtype

    def __eq__(self, __o: object) -> bool:
        return (
            isinstance(__o, Array)
            and __o.low == self.low
            and __o.high == self.high
            and __o.subtype == self.subtype
        )

    def __repr__(self) -> str:
        return f"array {self.low} .. {self.high} of {self.subtype}"


class WordArray(Type):
    def __init__(self, word_length: int, subtype: Type):
        self.word_length = word_length
        self.subtype = subtype

    def __eq__(self, __o: object) -> bool:
        return (
            isinstance(__o, WordArray)
            and __o.word_length == self.word_length
            and __o.subtype == self.subtype
        )

    def __repr__(self) -> str:
        return f"array word[{self.word_length}] of {self.subtype}"


class ModuleType(Type):
    def __init__(self, module_name: str, parameters: list[Expr]):
        self.module_name = module_name
        self.parameters = parameters

    def __eq__(self, __value: object) -> bool:
        """Two module types are equal if they are of the same module."""
        return type(__value) == ModuleType and __value.module_name == self.module_name

    def __hash__(self) -> int:
        return hash(self.module_name)

    def __repr__(self) -> str:
        return f"{self.module_name}({self.parameters})"


def is_integer_type(smv_type: Type) -> bool:
    return isinstance(smv_type, Integer) or (
        isinstance(smv_type, Enumeration) and smv_type.is_integer()
    )


def is_compatible_with(type1: Type, type2: Type) -> bool:
    if type1 == type2:
        return True

    if isinstance(type1, AnyType) or isinstance(type2, AnyType):
        return True

    return False


# type specifiers -------------------------


class Expr:
    def __init__(self, loc: Optional[log.FileLocation] = None) -> None:
        self.loc = loc
        self.type: Type = AnyType()


class Constant(Expr):
    def __init__(self, loc: Optional[log.FileLocation] = None) -> None:
        super().__init__(loc)


class IntegerConstant(Constant):
    def __init__(self, integer: int, loc: Optional[log.FileLocation] = None):
        super().__init__(loc)
        self.integer = integer
        self.type = Integer()

    def __repr__(self) -> str:
        return f"{self.integer}"


class BooleanConstant(Constant):
    def __init__(self, boolean: bool, loc: Optional[log.FileLocation] = None):
        super().__init__(loc)
        self.boolean = boolean
        self.type = Boolean()

    def __repr__(self) -> str:
        return f"{self.boolean}"


class WordConstant(Constant):
    def __init__(self, wconstant: str, loc: Optional[log.FileLocation] = None):
        super().__init__(loc)

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
        pre_underscore: str = spl[0][1:]  # stripping off the starting 0

        numbers_pre_underscore = re.findall(r"\d+", pre_underscore)
        if numbers_pre_underscore != []:
            self.width = int(numbers_pre_underscore[0])

        post_underscore: str = spl[1]

        self.value = post_underscore

        self.type = Word(self.width, self.signed)

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


class RangeConstant(Constant):
    def __init__(self, low: int, high: int, loc: Optional[log.FileLocation] = None):
        super().__init__(loc)
        self.low = low
        self.high = high
        self.type = Enumeration(set(range(low, high + 1)))

    def __repr__(self) -> str:
        return f"{self.low} .. {self.high}"


class FunCall(Expr):
    def __init__(
        self, name: str, args: list[Expr], loc: Optional[log.FileLocation] = None
    ):
        super().__init__(loc)
        self.name = name
        self.args = args

    def __repr__(self) -> str:
        return f"{self.name}({', '.join(str(a) for a in self.args)})"


class BinOp(Expr):
    def __init__(
        self, op: str, lhs: Expr, rhs: Expr, loc: Optional[log.FileLocation] = None
    ):
        super().__init__(loc)
        self.op = op
        self.lhs = lhs
        self.rhs = rhs

    def __repr__(self) -> str:
        return f"({self.lhs}) {self.op} ({self.rhs})"


class UnOp(Expr):
    def __init__(self, op: str, arg: Expr, loc: Optional[log.FileLocation] = None):
        super().__init__(loc)
        self.op = op
        self.arg = arg

    def __repr__(self) -> str:
        return f"{self.op} ({self.arg})"


class IndexSubscript(Expr):
    def __init__(
        self, array: Expr, index: Expr, loc: Optional[log.FileLocation] = None
    ):
        super().__init__(loc)
        self.array = array
        self.index = index

    def __repr__(self) -> str:
        return f"{self.array}[{self.index}]"


class WordBitSelection(Expr):
    def __init__(
        self, word: Expr, low: int, high: int, loc: Optional[log.FileLocation] = None
    ):
        super().__init__(loc)
        self.word = word
        self.low = low
        self.high = high

        # slices are always unsigned, see p19 of nuxmv user manual
        self.type = Word(high - low + 1, False)

    def __repr__(self) -> str:
        return f"{self.word}[{self.low} : {self.high}]"


class SetBodyExpression(Expr):
    def __init__(self, members: list[Expr], loc: Optional[log.FileLocation] = None):
        super().__init__(loc)
        self.members = members

    def __repr__(self) -> str:
        return f"set({self.members})"


class Ternary(Expr):
    def __init__(
        self,
        cond: Expr,
        then_expr: Expr,
        else_expr: Expr,
        loc: Optional[log.FileLocation] = None,
    ):
        super().__init__(loc)
        self.cond = cond
        self.then_expr = then_expr
        self.else_expr = else_expr

    def __repr__(self) -> str:
        return f"({self.cond}) ? ({self.then_expr}) : ({self.else_expr})"


class CaseExpr(Expr):
    def __init__(
        self, branches: list[tuple[Expr, Expr]], loc: Optional[log.FileLocation] = None
    ):
        super().__init__(loc)
        self.branches = branches

    def __repr__(self) -> str:
        branches = "\n".join(
            f"({cond}) : ({branch})" for (cond, branch) in self.branches
        )
        return f"case {branches} esac"


class ComplexIdentifier(Expr):
    def __init__(self, ident: str, loc: Optional[log.FileLocation] = None) -> None:
        super().__init__(loc)
        self.ident = ident

    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, ComplexIdentifier) and __o.ident == self.ident

    def __hash__(self) -> int:
        return hash(self.ident)


class Identifier(ComplexIdentifier):
    def __init__(self, ident: str, loc: Optional[log.FileLocation] = None):
        super().__init__(ident, loc)

    def __repr__(self) -> str:
        return f"{self.ident}"

    def __eq__(self, __o: object) -> bool:
        return type(__o) == Identifier and __o.ident == self.ident

    def __hash__(self) -> int:
        return hash(self.ident)


class ModuleAccess(ComplexIdentifier):
    def __init__(
        self,
        module: ComplexIdentifier,
        element: Identifier,
        loc: Optional[log.FileLocation] = None,
    ):
        super().__init__(module.ident, loc)
        self.module = module
        self.element = element

    def __eq__(self, __o: object) -> bool:
        return (
            type(__o) == ModuleAccess
            and __o.ident == self.ident
            and __o.module == self.module
            and __o.element == self.element
        )

    def __hash__(self) -> int:
        return hash((self.ident, self.module, self.element))

    def __repr__(self) -> str:
        return f"({self.module}.{self.element})"


class SymbolicConstant(Constant):
    def __init__(
        self, symbol: ComplexIdentifier, loc: Optional[log.FileLocation] = None
    ):
        super().__init__(loc)
        self.symbol = symbol

    def __repr__(self) -> str:
        return f"{self.symbol}"


class LTLProposition(Expr):
    def __init__(self, expr: Expr, loc: Optional[log.FileLocation] = None):
        super().__init__(loc)
        self.expr = expr

    def __repr__(self) -> str:
        return repr(self.expr)


# class ArrayAccess(ComplexIdentifier):
#     def __init__(self, array: Array, index):
#         self.array = array
#         self.index = index

#     def __repr__(self) -> str:
#         return f"{self.array}[{self.index}]"

# module elements -------------------------


# Module elements
class ModuleElement:
    pass


class VarDeclaration(ModuleElement):
    def __init__(self, var_list: list[tuple[Identifier, Type]], modifier: str):
        self.var_list = var_list
        match modifier:
            case "VAR":
                self.modifier = "VAR"
            case "IVAR":
                self.modifier = "IVAR"
            case "FROZENVAR":
                self.modifier = "FROZENVAR"
            case _:
                raise ValueError(
                    f"Invalid VAR modifier: {modifier} -- must be either `VAR`/`IVAR`/`FROZENVAR`"
                )

    def __repr__(self) -> str:
        def var_str(var: str, type: Type) -> str:
            return f"{var} : {type}"

        var_list_str = "\n".join(var_str(var[0].ident, var[1]) for var in self.var_list)
        return f"{self.modifier}\n" + var_list_str


class Function:
    def __init__(self, name: str, type: tuple[list[Type], Type]):
        self.name = name
        self.type = type

    def __repr__(self) -> str:
        domain = self.type[0]
        function_domain_str: str = str(domain[0])
        for d in domain[1:]:
            function_domain_str += "*" + str(d)
        function_type_str = f"{function_domain_str} -> {self.type[1]}"
        return f"{self.name} : {function_type_str}"


class FunctionDeclaration(ModuleElement):
    def __init__(self, function_list: list[Function]):
        self.function_list = function_list

    def __repr__(self) -> str:
        return f"FUN {self.function_list}"


class Define:
    def __init__(self, name: Identifier, expr: Expr):
        self.name = name
        self.expr = expr

    def __repr__(self) -> str:
        return f"{self.name} := {self.expr}"


class DefineDeclaration(ModuleElement):
    def __init__(self, define_list: list[Define]):
        self.define_list = define_list

    def __repr__(self) -> str:
        return f"DEFINE {self.define_list}"


class Constants:
    def __init__(self, identifier: ComplexIdentifier):
        self.identifier = identifier

    def __repr__(self) -> str:
        return f"{self.identifier}"


class ConstantsDeclaration(ModuleElement):
    def __init__(self, constants_list: list[Constants]):
        self.constants_list = constants_list

    def __repr__(self) -> str:
        return f"CONSTANTS {self.constants_list}"


class Assign:
    def __init__(self, lhs: ComplexIdentifier, rhs: Expr, modifier: str):
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
                raise ValueError(
                    f"Invalid Assign modifier: {self.modifier} -- must be either `init`/`next`/`none`"
                )


class AssignDeclaration(ModuleElement):
    def __init__(self, assign_list: list[Assign]):
        self.assign_list = assign_list

    def __repr__(self) -> str:
        return f"ASSIGN {self.assign_list}"


class TransDeclaration(ModuleElement):
    def __init__(self, formula: Expr):
        self.formula = formula

    def __repr__(self) -> str:
        return f"TRANS {self.formula}"


class InitDeclaration(ModuleElement):
    def __init__(self, formula: Expr):
        self.formula = formula

    def __repr__(self) -> str:
        return f"INIT {self.formula}"


class InvarDeclaration(ModuleElement):
    def __init__(self, formula: Expr):
        self.formula = formula

    def __repr__(self) -> str:
        return f"INVAR {self.formula}"


class JusticeDeclaration(ModuleElement):
    def __init__(self, formula: Expr):
        self.formula = formula

    def __repr__(self) -> str:
        return f"JUSTICE {self.formula}"


class InvarspecDeclaration(ModuleElement):
    def __init__(self, formula: Expr):
        self.formula = formula

    def __repr__(self) -> str:
        return f"INVARSPEC {self.formula}"


class LTLSpecDeclaration(ModuleElement):
    def __init__(self, formula: Expr, name: str):
        self.formula = formula
        self.name = name

    def __repr__(self) -> str:
        return f"LTLSPEC {self.formula}"


class PandaSpecDeclaration(ModuleElement):
    def __init__(self, formula: Expr):
        self.formula = formula

    def __repr__(self) -> str:
        return f"__PANDASPEC__ {self.formula}"


# module elements -------------------------


# top level -------------------------


class ModuleDeclaration:
    def __init__(self, name: str, parameters: list[str], elements: list[ModuleElement]):
        self.name = name
        self.parameters = parameters
        self.elements = elements

    def __eq__(self, __value: object) -> bool:
        return type(__value) == ModuleDeclaration and __value.name == self.name

    def __hash__(self) -> int:
        return hash(self.name)

    def __repr__(self) -> str:
        bodies = "\n".join(str(elem) for elem in self.elements) + "\n"
        if self.parameters == []:
            return f"\nMODULE {self.name}\n" + bodies
        return f"\nMODULE {self.name} ({self.parameters})\n" + bodies


class Program:
    def __init__(
        self, modules: list[ModuleDeclaration], main: Optional[ModuleDeclaration]
    ):
        self.modules = modules
        self.main = main

    def __repr__(self) -> str:
        return "\n".join(str(mod) for mod in self.modules)


class Context:
    def __init__(self, filename: str, modules: list[ModuleDeclaration]) -> None:
        # maps module name to all the variables it has, and then from those variables to their Types
        self.vars: dict[str, dict[str, Type]] = {m.name: {} for m in modules}
        self.frozen_vars: set[str] = set()
        self.defs: dict[str, dict[str, Expr]] = {m.name: {} for m in modules}
        self.init: list[Expr] = []
        self.invar: list[Expr] = []
        self.trans: list[Expr] = []

        # enum1: {s1, s2, s3}; enum2: {t1, t2} --> [[s1, s2, s3], [t1, t2]] (assume they're unique)
        self.enums: dict[str, Enumeration] = {}
        self.declared_enums: set[str] = set()

        # {s1 |-> enum1, s2 |-> enum1, s3 |-> enum1, t1 |-> enum2, t2 |-> enum2} (populated in translation)
        self.reverse_enums: dict[str, list[str]] = {}

        # maps {module_name |-> list of parameters (p1, t1), ...}, where pi is the variable and ti is its Type
        # we set this is type_check_module and check whether the module is in this dict to determine whether to add it --
        # so we don't initialize the full dict here
        self.module_params: dict[str, dict[str, Type]] = {}

        # maps {module_name |-> list of IL output variables} for use in submodule/local variable construction
        self.outputs: dict[str, list[tuple[str, moxi.Sort]]] = {}

        # maps {module_name |-> list of IL local variables} for use in submodule construction
        self.module_locals: dict[str, list[moxi.Variable]] = {}

        self.modules: dict[str, ModuleDeclaration] = {m.name: m for m in modules}
        self.module_deps: dict[ModuleDeclaration, set[ModuleDeclaration]] = {}

        # maps {module_name |-> set of definition identifiers} for output variable construction
        self.referenced_defs: dict[str, set[str]] = {m.name: set() for m in modules}

        self.cur_module: Optional[ModuleDeclaration] = None

        # List of expressions that must be type checked
        # Gets populated in first pass, then dealt with in second pass
        self.worklist: list[Expr] = []

        self.in_next_expr = False

        self.filename = filename
        self.lineno = 0
        self.err_msg_info = {"ifilename": self.filename, "ilineno": 0}

    def init_module(self, module: ModuleDeclaration):
        self.vars[module.name] = {}
        self.defs[module.name] = {}
        self.modules[module.name] = module
        self.referenced_defs[module.name] = set()

    def get_cur_module(self) -> ModuleDeclaration:
        if not self.cur_module:
            raise ValueError("cur_module not set in Context")
        return self.cur_module

    def get_cur_defs(self) -> dict[str, Expr]:
        return self.defs[self.get_cur_module().name]

    def get_module_dep_order(self, main: ModuleDeclaration) -> list[ModuleDeclaration]:
        stack: list[tuple[bool, ModuleDeclaration]] = []
        visited: set[ModuleDeclaration] = set()
        dep_order = collections.deque()

        stack.append((False, main))

        while len(stack) > 0:
            seen, cur = stack.pop()

            if seen:
                dep_order.append(cur)
                continue
            elif cur in visited:
                continue

            stack.append((True, cur))
            visited.add(cur)

            for dep in self.module_deps[cur]:
                stack.append((False, dep))

        return list(dep_order)


def postorder(expr: Expr, context: Context, traverse_defs: bool):
    """Perform an iterative postorder traversal of 'expr'."""
    stack: list[tuple[bool, Expr]] = []
    visited: set[int] = set()

    stack.append((False, expr))

    while len(stack) > 0:
        (seen, cur) = stack.pop()

        if seen:
            yield cur

            if isinstance(cur, FunCall) and cur.name == "next":
                context.in_next_expr = False

            continue
        elif id(cur) in visited:
            continue

        visited.add(id(cur))
        stack.append((True, cur))

        match cur:
            case Identifier(
                ident=ident
            ) if traverse_defs and ident in context.get_cur_defs():
                stack.append((False, context.get_cur_defs()[ident]))
            case FunCall(args=args):
                if cur.name == "next":
                    context.in_next_expr = True
                [stack.append((False, arg)) for arg in args]
            case UnOp(arg=arg):
                stack.append((False, arg))
            case BinOp(lhs=lhs, rhs=rhs):
                stack.append((False, lhs))
                stack.append((False, rhs))
            case IndexSubscript(array=array, index=index):
                stack.append((False, array))
                stack.append((False, index))
            case WordBitSelection(word=word, low=_, high=_):
                stack.append((False, word))
            case SetBodyExpression(members=members):
                [stack.append((False, m)) for m in members]
            case Ternary(cond=cond, then_expr=then_expr, else_expr=else_expr):
                stack.append((False, cond))
                stack.append((False, then_expr))
                stack.append((False, else_expr))
            case CaseExpr(branches=branches):
                for cond, then_expr in branches:
                    stack.append((False, cond))
                    stack.append((False, then_expr))
            case ModuleAccess(module=module):
                stack.append((False, module))
            case _:
                pass


def type_check_expr(
    top_expr: Expr, context: Context, cur_module: ModuleDeclaration
) -> bool:
    # see starting on p16 of nuxmv user manual
    # print(f"type_check_expr({expr})")
    def error(msg: str, expr: Expr) -> bool:
        log.error(msg, FILE_NAME, location=expr.loc)
        return False

    for expr in postorder(top_expr, context, True):
        match expr:
            case IntegerConstant():
                pass
            case BooleanConstant():
                pass
            case SymbolicConstant():
                pass
            case WordConstant():
                pass
            case RangeConstant():
                pass
            case LTLProposition(expr=arg):
                expr.type = Boolean()
            case FunCall(name="next", args=args):
                if len(args) != 1:
                    return error(
                        f"`next` expr only allowed one operand\n\t{expr}", expr
                    )

                expr.type = args[0].type
            case FunCall(name="signed", args=args):
                if len(args) != 1:
                    return error(
                        f"`signed` expr only allowed one operand\n\t{expr}", expr
                    )

                arg: Expr = args[0]

                if not isinstance(arg.type, Word):
                    return error(f"Invalid argument for 'signed' {arg}\n\t{expr}", expr)

                if arg.type.signed:
                    return error(
                        f"Argument to `signed` must be unsigned word\n\t{expr}", expr
                    )

                expr.type = Word(width=arg.type.width, signed=True)
            case FunCall(name="unsigned", args=args):
                if len(args) != 1:
                    return error(
                        f"`unsigned` expr only allowed one operand\n\t{expr}", expr
                    )

                arg: Expr = args[0]

                if not isinstance(arg.type, Word):
                    return error(f"Invalid argument for 'signed' {arg}\n\t{expr}", expr)

                if not arg.type.signed:
                    return error(
                        f"Argument to `signed` must be signed word\n\t{expr}", expr
                    )

                expr.type = Word(width=arg.type.width, signed=False)
            case FunCall(name="READ", args=args):
                if len(args) != 2:
                    return error(f"'READ' expr must have 2 operands\n\t{expr}", expr)

                (arr, idx) = args

                match arr.type:
                    case Array():
                        if not isinstance(idx.type, Integer):
                            return error(
                                f"'READ' expr index must be of integer type\n\t{expr}",
                                expr,
                            )
                    case WordArray():
                        if not isinstance(idx.type, Word):
                            return error(
                                f"'READ' expr index must be of word type\n\t{expr}",
                                expr,
                            )
                    case _:
                        return error(
                            f"'READ' expr must apply to array type, found {arr.type}\n\t{expr}",
                            expr,
                        )

                expr.type = arr.type.subtype
            case FunCall(name="WRITE", args=args):
                if len(args) != 3:
                    return error(f"'WRITE' expr must have 3 operands\n\t{expr}", expr)

                (arr, idx, val) = args

                match arr.type:
                    case Array(subtype=subtype):
                        if not isinstance(idx.type, Integer):
                            return error(
                                f"'WRITE' expr index must be of integer type\n\t{expr}",
                                expr,
                            )
                    case WordArray(subtype=subtype):
                        if not isinstance(idx.type, Word):
                            return error(
                                f"'WRITE' expr index must be of word type\n\t{expr}",
                                expr,
                            )
                    case _:
                        return error(
                            f"'WRITE' expr must apply to array type, found {arr.type}\n\t{expr}",
                            expr,
                        )

                if val.type != subtype:
                    return error(
                        f"'WRITE' expr value must be same as array subtype, found {val.type}\n\t{expr}",
                        expr,
                    )

                expr.type = arr.type
            case FunCall(name="typeof", args=args):
                if len(args) != 1:
                    return error(
                        f"'typeof' operator only allowed one operand\n\t{expr}", expr
                    )

                expr.type = args[0].type
            case FunCall(name="CONSTARRAY", args=args):
                if len(args) != 2:
                    return error(
                        f"'CONSTARRAY' requires 2 operands, got {len(args)}", expr
                    )

                const_type, const_val = args

                if not isinstance(const_type, FunCall) or const_type.name != "typeof":
                    return error(
                        f"'CONSTARRAY' first operand must be 'typeof', found {const_type}\n\t{expr}",
                        expr,
                    )

                if not isinstance(const_type.type, (Array, WordArray)):
                    return error(
                        f"'CONSTARRAY' first operand must be of array type, found {const_type.type}\n\t{expr}",
                        expr,
                    )

                if const_val.type != const_type.type.subtype:
                    return error(
                        f"'CONSTARRAY' operands must match types {const_type.type}, {const_val.type}\n\t{expr}",
                        expr,
                    )

                expr.type = const_type.type
            case FunCall(name=name, args=args):
                return error(f"Unsupported function {name}", expr)
            case UnOp(op=op, arg=arg):
                if isinstance(arg.type, (Real, Clock)):
                    return error(
                        f"Unsupported type for {arg}, {arg.type}\n\t{expr}", expr
                    )

                match (op, arg.type):
                    case ("!", Boolean()) | ("!", Word()):
                        expr.type = arg.type
                    case ("-", Boolean()) | ("-", Word()) | ("-", Integer()):
                        expr.type = arg.type
                    case (
                        ("X", Boolean())
                        | ("G", Boolean())
                        | ("F", Boolean())
                        | ("Y", Boolean())
                        | ("H", Boolean())
                        | ("O", Boolean())
                    ):
                        expr.type = arg.type
                    case _:
                        return error(
                            f"Type checking error for {op}: {arg.type}\n\t{expr}", expr
                        )
            case BinOp(op=op, lhs=lhs, rhs=rhs):
                if isinstance(lhs.type, (Real, Clock)):
                    return error(
                        f"Unsupported type for {lhs}, {lhs.type}\n\t{expr}", expr
                    )
                elif isinstance(rhs.type, (Real, Clock)):
                    return error(
                        f"Unsupported type for {rhs}, {rhs.type}\n\t{expr}", expr
                    )

                if op in {"&", "|", "xor", "xnor", "->", "<->"}:
                    match (lhs.type, rhs.type):
                        case (Boolean(), Boolean()):
                            expr.type = Boolean()
                        case (Word(width=w1, signed=s1), Word(width=w2, signed=s2)):
                            if w1 != w2 or s1 != s2:
                                return error(
                                    f"Words not of same width and sign {expr}, {lhs.type} {rhs.type}\n\t{expr}",
                                    expr,
                                )
                            expr.type = Word(w1, s1)
                        case _:
                            return error(
                                f"Type checking error for {op} ({lhs.type}, {rhs.type})\n\t{expr}",
                                expr,
                            )
                elif op in {"=", "!=", ">", "<", ">=", "<="}:
                    match (lhs.type, rhs.type):
                        case (Boolean(), Boolean()):
                            expr.type = Boolean()
                        case (Integer(), Integer()):
                            expr.type = Boolean()
                        case (Enumeration(), Integer()):
                            if not lhs.type.is_integer():
                                return error(
                                    f"Expressions not of same type ({lhs.type}, {rhs.type})\n\t{expr}",
                                    expr,
                                )
                            expr.type = Boolean()
                        case (Integer(), Enumeration()):
                            if not rhs.type.is_integer():
                                return error(
                                    f"Expressions not of same type ({lhs.type}, {rhs.type})\n\t{expr}",
                                    expr,
                                )
                            expr.type = Boolean()
                        case (Word(width=w1, signed=s1), Word(width=w2, signed=s2)):
                            if w1 != w2 or s1 != s2:
                                return error(
                                    f"Words not of same width and sign ({lhs.type}, {rhs.type})\n\t{expr}",
                                    expr,
                                )
                            expr.type = Boolean()
                        case (
                            Array(low=low1, high=high1, subtype=type1),
                            Array(low=low2, high=high2, subtype=type2),
                        ):
                            if low1 != low2 and high1 != high2 and type1 != type2:
                                return error(
                                    f"Different array types ({lhs.type}, {rhs.type})\n\t{expr}",
                                    expr,
                                )
                            expr.type = Boolean()
                        case (
                            WordArray(word_length=wl1, subtype=type1),
                            WordArray(word_length=wl2, subtype=type2),
                        ):
                            if wl1 != wl2 and type1 != type2:
                                return error(
                                    f"Different array types ({lhs.type}, {rhs.type})\n\t{expr}",
                                    expr,
                                )
                            expr.type = Boolean()
                        case (Enumeration(), Enumeration()):
                            lhs_type = cast(Enumeration, lhs.type)
                            rhs_type = cast(Enumeration, rhs.type)

                            if op == "=" or op == "!=":
                                pass
                            elif not lhs_type.is_integer() or not rhs_type.is_integer():
                                return error(
                                    f"Expressions not of same type ({lhs.type}, {rhs.type})\n\t{expr}",
                                    expr,
                                )

                            expr.type = Boolean()
                        case _:
                            return error(
                                f"Type check error for {expr} ({lhs.type}, {rhs.type})",
                                expr,
                            )
                elif op in {"+", "-", "*", "/", "mod"}:
                    match (lhs.type, rhs.type):
                        case (Integer(), Integer()):
                            expr.type = Integer()
                        case (Enumeration(), Integer()):
                            if not lhs.type.is_integer():
                                return error(
                                    f"Expressions not of same type ({lhs.type}, {rhs.type})\n\t{expr}",
                                    expr,
                                )
                            expr.type = Integer()
                        case (Integer(), Enumeration()):
                            if not rhs.type.is_integer():
                                return error(
                                    f"Expressions not of same type ({lhs.type}, {rhs.type})\n\t{expr}",
                                    expr,
                                )
                            expr.type = Integer()
                        case (Word(width=w1, signed=s1), Word(width=w2, signed=s2)):
                            if w1 != w2 or s1 != s2:
                                return error(
                                    f"Words not of same width and sign ({lhs.type}, {rhs.type})\n\t{expr}",
                                    expr,
                                )
                            expr.type = Word(w1, s1)
                        case _:
                            return error(
                                f"Type check error ({lhs.type}, {rhs.type})\n\t{expr}",
                                expr,
                            )
                elif op in {"<<", ">>"}:
                    match (lhs.type, rhs.type):
                        case (Word(width=w, signed=s), Integer()):
                            expr.type = Word(width=w, signed=s)
                        case (Word(width=w1, signed=s), Word(width=w2, signed=False)):
                            expr.type = Word(width=w1, signed=s)
                        case _:
                            return error(
                                f"Type check error ({lhs.type}, {rhs.type})\n\t{expr}",
                                expr,
                            )
                elif op in {"concat"}:
                    match (lhs.type, rhs.type):
                        case (Word(width=w1, signed=s1), Word(width=w2, signed=s2)):
                            expr.type = Word(width=w1 + w2, signed=False)
                        case _:
                            return error(
                                f"Type check error ({lhs.type}, {rhs.type})\n\t{expr}",
                                expr,
                            )
                else:
                    return error(f"Unsupported op `{op}`, `{expr}`", expr)
            case IndexSubscript():
                return error(f"Unsupported operator {type(expr)}", expr)
            case WordBitSelection(word=word, low=low, high=high):
                if not isinstance(word.type, Word):
                    return error(
                        f"Bit select only valid on words, found '{word.type}'\n\t{expr}",
                        expr,
                    )

                if low < 0:
                    return error(
                        f"Low value for bit select must be greater than 0 ({low})\n\t{expr}",
                        expr,
                    )

                if high >= word.type.width:
                    return error(
                        f"High value for bit select must be less than word width, {high} >= {word.type.width}\n\t{expr}",
                        expr,
                    )

                if low > high:
                    return error(
                        f"High value for bit select must be greater than low value [{low}:{high}]\n\t{expr}",
                        expr,
                    )
            case SetBodyExpression():
                return error(f"Unsupported operator {type(expr)}\n\t{expr}", expr)
            case Ternary(cond=cond, then_expr=then_expr, else_expr=else_expr):
                if cond.type != Boolean():
                    return error(
                        f"Condition of ternary must be boolean, found '{cond.type}'\n\t{expr}",
                        expr,
                    )

                if then_expr.type != else_expr.type:
                    return error(
                        f"Branches of ternary not the same."
                        f"\n\tFound '{then_expr.type}' and '{else_expr.type}"
                        f"\n\t{expr}",
                        expr,
                    )

                expr.type = then_expr.type
            case CaseExpr(branches=branches):
                for cond, branch in branches:
                    if not isinstance(cond.type, Boolean) and not (
                        isinstance(cond.type, Word) and cond.type.width == 1
                    ):
                        return error(
                            f"Case condition must be boolean, found {cond.type}\n\t{expr}",
                            expr,
                        )

                    # TODO: check that branches all have same type
                    expr.type = branch.type
            case Identifier(ident=ident):
                # print(f"{context.module_params[cur_module.name]}, {expr.ident}")
                # print(expr.ident in context.module_params[cur_module.name])

                if ident in context.vars[cur_module.name]:
                    expr.type = context.vars[cur_module.name][ident]
                elif ident in context.defs[cur_module.name]:
                    expr.type = context.defs[cur_module.name][ident].type
                elif expr.ident in context.module_params[cur_module.name]:
                    expr.type = context.module_params[cur_module.name][expr.ident]
                else:
                    # TODO:
                    # Currently this finds the first enum that this ident is a member of.
                    # But nuXmv enums are odd -- currently we declare a new enum sort for each
                    # enum that is declared.
                    # Really we want one enum sort for every enum and introduce invariants that say what
                    # values some variables cannot be.
                    # This is because enums of different "types" can be compared and be equal in nuXmv.
                    flag = False
                    for enum in context.enums.values():
                        if ident in enum.summands:
                            expr.type = Enumeration(summands=set(enum.summands))
                            flag = True

                    if not flag:
                        return error(f"Variable {expr} not declared", expr)

            case ModuleAccess(module=module, element=element):
                if not isinstance(module.type, ModuleType):
                    return error(f"Not a module '{module}'\n\t{expr}", expr)

                module_name = module.type.module_name

                if element.ident in context.vars[module_name]:
                    expr.type = context.vars[module_name][element.ident]
                elif element.ident in context.module_params[module_name]:
                    expr.type = context.module_params[module_name][element.ident]
                elif element.ident in context.defs[module_name]:
                    expr.type = context.defs[module_name][element.ident].type
                    context.referenced_defs[module_name].add(element.ident)
                else:
                    return error(
                        f"{module}.{element}: {element} not a variable or parameter",
                        expr,
                    )
            case _:
                return error(f"Unsupported operator {type(expr)}\n\t{expr}", expr)

        if expr.type == AnyType():
            return error(f"Type check error\n\t{expr}", expr)

    return True


def type_check_module(module: ModuleDeclaration, context: Context) -> bool:
    log.debug(2, f"Type checking module '{module.name}'", FILE_NAME)

    status = True

    context.cur_module = module

    context.module_deps[module] = set()

    context.vars[module.name] = {}
    context.defs[module.name] = {}

    if module.name not in context.module_params:
        context.module_params[module.name] = {}

    # Forward references are allowed....ugh
    # First we go thru each element of the module and collect every declared variable/define
    for element in module.elements:
        match element:
            case VarDeclaration(var_list=var_list, modifier=modifier):
                for smv_id, smv_type in var_list:
                    context.vars[module.name][smv_id.ident] = smv_type

                    if modifier == "FROZENVAR":
                        context.frozen_vars.add(smv_id.ident)

                    if isinstance(smv_type, Enumeration):
                        if smv_type.is_integers_and_symbolic():
                            log.error(
                                "integers-and-symbolic enums unsupported", FILE_NAME
                            )
                            status = False

                        if repr(smv_type) in context.declared_enums:
                            continue

                        new_sym: str = fresh_symbol("enum")
                        context.enums[new_sym] = smv_type
                        context.declared_enums.add(repr(smv_type))

                        set_list: list[str | int] = list(smv_type.summands)
                        str_set_list: list[str] = [str(s) for s in set_list]

                        for st in str_set_list:
                            if st in context.reverse_enums:
                                context.reverse_enums[st].append(new_sym)
                            else:
                                context.reverse_enums[st] = [new_sym]
            case DefineDeclaration(define_list=define_list):
                for define in define_list:
                    context.defs[module.name][define.name.ident] = define.expr
            case _:
                pass

    for var_decl in [vd for vd in module.elements if isinstance(vd, VarDeclaration)]:
        for var_name, smv_type in [
            (var_name, smv_type)
            for var_name, smv_type in var_decl.var_list
            if isinstance(smv_type, ModuleType)
        ]:
            log.debug(2, 
                f"Module instantiation of '{smv_type.module_name}' ({var_name})",
                FILE_NAME,
            )
            signature: list[Type] = []

            for param in smv_type.parameters:
                status = status and type_check_expr(
                    top_expr=param, context=context, cur_module=module
                )
                signature.append(param.type)

            target_module = context.modules[smv_type.module_name]
            context.module_deps[module].add(target_module)

            if smv_type.module_name not in context.module_params:
                # first time instantiating this module type -- this is now the enforced signature
                target_module = context.modules[smv_type.module_name]

                if len(target_module.parameters) != len(signature):
                    log.error(
                        f"Invalid number of parameters provided in module instantiation '{var_name}'."
                        f"\n\tExpected {len(target_module.parameters)}, got {len(signature)}",
                        FILE_NAME,
                    )
                    return False

                context.module_params[smv_type.module_name] = {
                    param: smv_type
                    for param, smv_type in zip(target_module.parameters, signature)
                }

                # we only type check modules if they are instantiated -- this is how nuXmv works too
                status = status and type_check_module(target_module, context)
                context.cur_module = module

                log.debug(2, f"Done with module '{target_module.name}'", FILE_NAME)

                continue

            module_signature = context.module_params[smv_type.module_name].values()

            if len(signature) != len(module_signature):
                log.error(
                    f"Invalid number of parameters provided in module instantiation '{var_name}'."
                    f"\n\tExpected {len(module_signature)}, got {len(signature)}",
                    FILE_NAME,
                )
                status = False

            # MUST report if user is trying to dynamically type the module instantiations
            # since nuXmv won't yell at them for it and we don't support it
            for p1, p2 in zip(signature, module_signature):
                if p1 != p2:
                    log.error(
                        f"Parameter types for module instantiation disagree '{var_name}', modules must be statically typed."
                        f"\n\tExpected {' '.join([repr(m) for m in module_signature])}"
                        f"\n\tGot {' '.join([repr(s) for s in signature])}",
                        FILE_NAME,
                    )
                    status = False

    # Now type check each expression
    for element in module.elements:
        match element:
            case DefineDeclaration(define_list=define_list):
                for define in reversed(define_list):
                    # TODO: is the check below helpful?
                    if define.expr.type == AnyType():
                        log.debug(2, f"Type checking DEFINE {define.name}", FILE_NAME)
                        status = status and type_check_expr(
                            define.expr, context, module
                        )
            case AssignDeclaration(assign_list=assign_list):
                for assign in assign_list:
                    status = status and type_check_expr(assign.rhs, context, module)
            case TransDeclaration(formula=formula):
                status = status and type_check_expr(formula, context, module)
                context.trans.append(formula)
            case InitDeclaration(formula=formula):
                status = status and type_check_expr(formula, context, module)
                context.init.append(formula)
            case InvarDeclaration(formula=formula):
                status = status and type_check_expr(formula, context, module)
                context.invar.append(formula)
            case JusticeDeclaration(formula=formula):
                status = status and type_check_expr(formula, context, module)
            case InvarspecDeclaration(formula=formula):
                status = status and type_check_expr(formula, context, module)
            case LTLSpecDeclaration(formula=formula):
                log.debug(2, f"Typing checking {formula}", FILE_NAME)
                status = status and type_check_expr(formula, context, module)
            case PandaSpecDeclaration(formula=formula):
                status = status and type_check_expr(formula, context, module)
            case _:
                pass

    return status
