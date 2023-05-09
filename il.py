from __future__ import annotations
import sys
from typing import Any, Callable, NewType

from btor2 import *


class ILAttribute(Enum):
    INPUT      = ":input"
    OUTPUT     = ":output"
    LOCAL      = ":local"
    INIT       = ":init"
    TRANS      = ":trans"
    INV        = ":inv"
    ASSUMPTION = ":assumption"
    FAIRNESS   = ":fairness"
    REACHABLE  = ":reachable"
    CURRENT    = ":current"
    QUERY      = ":query"


class ILIdentifier():
    """
    An identifier is a symbol and can be "indexed" with numerals. As opposed to SMT-LIB2, we restrict indices to numerals and not symbols and numerals.

    See section 3.3 of https://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2021-05-12.pdf.
    """

    def __init__(self, symbol: str, indices: list[int]):
        self.symbol = symbol
        self.indices = indices

    def __eq__(self, __value: object) -> bool:
        """Two ILIdentifiers are equal if they have the same symbol and indices."""
        if not isinstance(__value, ILIdentifier):
            return False

        if self.symbol != __value.symbol:
            return False

        if len(self.indices) != len(__value.indices):
            return False 

        for i in range(0, len(self.indices)):
            if self.indices[i] != __value.indices[i]:
                return False
            
        return True

    def __hash__(self) -> int:
        return hash(self.symbol) + sum([hash(i) for i in self.indices])

    def __str__(self) -> str:
        if len(self.indices) == 0:
            return self.symbol

        s = f"(_ {self.symbol} "
        for index in self.indices:
            s += f"{index} "
        return s[:-1]+")"


class ILSort():

    def __init__(self, identifier: ILIdentifier, sorts: list[ILSort]):
        self.identifier = identifier
        self.sorts = sorts

    def arity(self) -> int:
        return len(self.sorts)

    def __eq__(self, __value: object) -> bool:
        return isinstance(__value, ILSort) and self.identifier == __value.identifier
    
    def __hash__(self) -> int:
        return hash(self.identifier)
    
    def __str__(self) -> str:
        s = f"({self.identifier} "
        for sort in self.sorts:
            s += f"{sort} "
        return s[:-1]+")"


# Built-in sorts
IL_NO_SORT: ILSort = ILSort(ILIdentifier("", []), []) # placeholder sort
IL_BOOL_SORT: ILSort = ILSort(ILIdentifier("Bool", []), [])
IL_BITVEC_SORT: Callable[[int], ILSort] = lambda n: ILSort(ILIdentifier("BitVec", [n]), [])


def is_bv_sort(sort: ILSort) -> bool:
    """A bit vector sort has an identifier with the symbol 'BitVec' and is indexed with a single numeral."""
    if sort.identifier.symbol != "BitVec" or len(sort.sorts) != 0 or len(sort.identifier.indices) != 1:
        return False
    return True


class ILExpr():

    def __init__(self, sort: ILSort, children: list[ILExpr]):
        self.sort = sort
        self.children = children

    def __hash__(self) -> int:
        return id(self)
        

class ILConstant(ILExpr):

    def __init__(self, sort: ILSort, value: Any):
        super().__init__(sort, [])
        self.value = value

    def __str__(self) -> str:
        return f"{self.value}"


class ILVar(ILExpr):
    """An ILVar requires a sort and symbol."""

    def __init__(self, sort: ILSort, symbol: str):
        super().__init__(sort, [])
        self.symbol = symbol

    def __eq__(self, __value: object) -> bool:
        """Two ILVars are equal if they have the same symbol."""
        if isinstance(__value, ILVar):
            return self.symbol == __value.symbol
        return False

    def __hash__(self) -> int:
        return hash(self.symbol)

    def __str__(self) -> str:
        return f"{self.symbol}"



class ILInputVar(ILVar):

    def __init__(self, sort: ILSort, symbol: str, prime: bool):
        super().__init__(sort, symbol)
        self.prime = prime

    def rename(self, new: str) -> ILInputVar:
        return ILInputVar(self.sort, new, self.prime)


class ILOutputVar(ILVar):

    def __init__(self, sort: ILSort, symbol: str, prime: bool):
        super().__init__(sort, symbol)
        self.prime = prime

    def __str__(self) -> str:
        return super().__str__() + ("'" if self.prime else "")

    def rename(self, new: str) -> ILOutputVar:
        return ILOutputVar(self.sort, new, self.prime)


class ILLocalVar(ILVar):

    def __init__(self, sort: ILSort, symbol: str, prime: bool):
        super().__init__(sort, symbol)
        self.prime = prime

    def __str__(self) -> str:
        return super().__str__() + ("'" if self.prime else "")

    def rename(self, new: str) -> ILLocalVar:
        return ILLocalVar(self.sort, new, self.prime)


class ILLogicVar(ILVar):

    def __init__(self, sort: ILSort, symbol: str):
        super().__init__(sort, symbol)

    def rename(self, new: str) -> ILLogicVar:
        return ILLogicVar(self.sort, new)


class ILApply(ILExpr):

    def __init__(self, sort: ILSort, identifier: ILIdentifier, children: list[ILExpr]):
        super().__init__(sort, children)
        self.identifier = identifier

    def __str__(self) -> str:
        s = f"({self.identifier} "
        for child in self.children:
            s += f"{child} "
        return s[:-1] + ")"


class ILSystem():
    
    def __init__(
        self, 
        input: list[ILVar], 
        state: list[ILVar],
        output: list[ILVar], 
        init: ILExpr,
        trans: ILExpr, 
        inv: ILExpr
    ):
        self.input = input
        self.state = state
        self.output = output
        self.init = init
        self.trans = trans
        self.inv = inv


class ILCommand():
    pass


class ILDeclareSort(ILCommand):

    def __init__(self, symbol: str, arity: int):
        super().__init__()
        self.symbol = symbol
        self.arity = arity


class ILDefineSort(ILCommand):

    def __init__(self, symbol: str, definition: ILSort):
        super().__init__()
        self.symbol = symbol
        self.definition = definition


class ILDeclareConst(ILCommand):

    def __init__(self, symbol: str, sort: ILSort):
        super().__init__()
        self.symbol = symbol
        self.sort = sort


class ILDefineSystem(ILCommand):
    
    def __init__(
        self, 
        symbol: str,
        input: list[tuple[str, ILSort]], 
        output: list[tuple[str, ILSort]], 
        local: list[tuple[str, ILSort]],
        init: ILExpr,
        trans: ILExpr, 
        inv: ILExpr,
        subsystems: list[tuple[str, ILDefineSystem]]
    ):
        self.symbol = symbol
        self.input = input
        self.local = local
        self.output = output
        self.init = init
        self.trans = trans
        self.inv = inv
        self.subsystems = subsystems


class ILCheckSystem(ILCommand):
    
    def __init__(
        self, 
        sys_symbol: str,
        input: list[tuple[str, ILSort]], 
        output: list[tuple[str, ILSort]], 
        local: list[tuple[str, ILSort]],
        assumption: dict[str, ILExpr],
        fairness: dict[str, ILExpr], 
        reachable: dict[str, ILExpr], 
        current: dict[str, ILExpr], 
        query: dict[str, list[str]], 
    ):
        self.sys_symbol = sys_symbol
        self.input = input
        self.output = output
        self.local = local
        self.assumption = assumption
        self.fairness = fairness
        self.reachable = reachable
        self.current = current
        self.query = query
        self.var_map: dict[str, str] = {}


class ILExit(ILCommand):
    pass


class ILLogic():

    def __init__(
        self, 
        name: str, 
        sort_symbols: dict[str, tuple[int, int]], 
        function_symbols: set[str],
        sort_check: Callable[[ILApply], bool]
    ):
        self.name = name
        self.sort_symbols = sort_symbols
        self.function_symbols = function_symbols
        self.sort_check = sort_check


def sort_check_apply_bv(node: ILApply) -> bool:
    """Returns true if `node` corresponds to a valid function signature in SMT-LIB2 QF_BV logic."""
    function = node.identifier

    if function.symbol == "=":
        # (= (_ BitVec m) (_ BitVec m) Bool)
        if len(function.indices) != 0:
            return False

        if len(node.children) != 2:
            return False

        if not is_bv_sort(node.children[0].sort) or not is_bv_sort(node.children[1].sort):
            return False

        m = node.children[0].sort.identifier.indices[0]
        if m != node.children[1].sort.identifier.indices[0]:
            return False

        node.sort = IL_BOOL_SORT

        return True
    elif function.symbol == "extract":
        # ((_ extract i j) (_ BitVec m) (_ BitVec n))
        if len(function.indices) != 2:
            return False
        
        i,j = function.indices[0], function.indices[1]

        if len(node.children) != 1 or not is_bv_sort(node.children[0].sort):
            return False

        m = node.children[0].sort.identifier.indices[0]
        if not i <= m and j <= i:
            return False

        node.sort = IL_BITVEC_SORT(i-j+1)

        return True
    elif function.symbol == "bvnot":
        # (bvnot (_ BitVec m) (_ BitVec m))
        if len(function.indices) != 0:
            return False
        
        if len(node.children) != 1 or not is_bv_sort(node.children[0].sort):
            return False

        m = node.children[0].sort.identifier.indices[0]
        node.sort = IL_BITVEC_SORT(m)

        return True
    elif function.symbol == "bvand" or function.symbol == "bvadd" or function.symbol == "bvsmod":
        # (bvand (_ BitVec m) (_ BitVec m) (_ BitVec m))
        if len(function.indices) != 0:
            return False
        
        if len(node.children) != 2 or not is_bv_sort(node.children[0].sort) or not is_bv_sort(node.children[1].sort):
            return False

        m = node.children[0].sort.identifier.indices[0]
        node.sort = IL_BITVEC_SORT(m)

        return True

    return False


FUNCTIONS_BV = {"=", "extract", "bvnot", "bvand", "bvadd", "bvsmod"}
QF_BV = ILLogic("QF_BV", {"BitVec": (1,0)}, FUNCTIONS_BV, sort_check_apply_bv)

FuncSig = NewType("FuncSig", tuple[list[ILSort], ILSort])


class ILContext():

    def __init__(self):
        self.declared_sorts: dict[ILIdentifier, int] = {}
        self.defined_sorts: set[ILSort] = set()
        self.declared_functions: dict[str, FuncSig] = {}
        self.defined_functions: dict[str, tuple[FuncSig, ILExpr]] = {}
        self.defined_systems: dict[str, ILDefineSystem] = {}
        self.logic = QF_BV # for now, assume QF_BV logic

    def get_symbols(self) -> set[str]:
        symbols = set()

        symbols.update([id.symbol for id in self.declared_sorts])
        symbols.update([srt.identifier.symbol for srt in self.defined_sorts])
        symbols.update([sym for sym in self.declared_functions])
        symbols.update([sym for sym in self.defined_functions])
        symbols.update([sym for sym in self.defined_systems])

        return symbols


class ILProgram():

    def __init__(self, commands: list[ILCommand]):
        self.commands: list[ILCommand] = commands

    def get_check_systems(self) -> list[ILCheckSystem]:
        return [cmd for cmd in self.commands if isinstance(cmd, ILCheckSystem)]


def postorder_iterative(expr: ILExpr, func: Callable[[ILExpr], Any]):
    """Perform an iterative postorder traversal of `expr`, calling `func` on each node."""
    stack: list[tuple[bool, ILExpr]] = []
    visited: set[int] = set()

    stack.append((False, expr))

    while len(stack) > 0:
        cur = stack.pop()

        if cur[0]:
            func(cur[1])
            continue
        elif id(cur[1]) in visited:
            continue

        visited.add(id(cur[1]))
        stack.append((True, cur[1]))
        for child in cur[1].children:
            stack.append((False, child))


def sort_check(program: ILProgram) -> tuple[bool, ILContext]:
    context: ILContext = ILContext()
    status: bool = True

    def sort_check_expr(node: ILExpr, no_prime: bool, prime_input: bool) -> bool:
        """Return true if node is well-sorted where `no_prime` is true if primed variables are disabled and `prime_input` is true if input variable are allowed to be primed (true for check-system assumptions and reachability conditions). """
        nonlocal context

        if isinstance(node, ILConstant):
            return True
        if isinstance(node, ILInputVar):
            if node.prime and not prime_input:
                print(f"Error: primed input variables only allowed in check system assumptions and reachability conditions ({node.symbol}).")
                return False

            return True
        elif isinstance(node, ILOutputVar) or isinstance(node, ILLocalVar):
            if node.prime and no_prime:
                print(f"Error: primed variables only allowed in system transition relation ({node.symbol}).")
                return False

            return True
        elif isinstance(node, ILApply):
            arg_sorts: list[ILSort] = []
            return_sort: ILSort = IL_NO_SORT

            if node.identifier.symbol in context.logic.function_symbols:
                for arg in node.children:
                    sort_check_expr(arg, no_prime, prime_input)
                return context.logic.sort_check(node)
            elif node.identifier.symbol in context.defined_functions:
                ((arg_sorts, return_sort), expr) = context.defined_functions[node.identifier.symbol]

                if len(arg_sorts) != len(node.children):
                    print(f"Error: function args do not match definition ({node}).")
                    return False

                for i in range(0, len(arg_sorts)):
                    sort_check_expr(node.children[i], no_prime, prime_input)
                    if arg_sorts[i] != node.children[i].sort:
                        print(f"Error: function args do not match definition ({node}).")
                        return False
            else:
                print(f"Error: symbol `{node.identifier.symbol}` not recognized.")
                return False

            node.sort = return_sort
            return True

        print(f"Error: node type `{node.__class__}` not recognized.")
        return False
    # end sort_check_expr

    for cmd in program.commands:
        if isinstance(cmd, ILDeclareSort):
            if cmd.symbol in context.get_symbols():
                print(f"Error: symbol `{cmd.symbol}` already in use.")
                status = False

            # TODO
        elif isinstance(cmd, ILDefineSort):
            if cmd.symbol in context.get_symbols():
                print(f"Error: symbol `{cmd.symbol}` already in use.")
                status = False

            # TODO
        elif isinstance(cmd, ILDeclareConst):
            if cmd.symbol in context.get_symbols():
                print(f"Error: symbol `{cmd.symbol}` already in use.")
                status = False

            context.declared_functions[cmd.symbol] = FuncSig(([], cmd.sort))
        elif isinstance(cmd, ILDefineSystem):
            # TODO: check for variable name clashes across cmd.input, cmd.output, cmd.local

            context.defined_systems[cmd.symbol] = cmd

            status = status and sort_check_expr(cmd.init, True, False)
            status = status and sort_check_expr(cmd.trans, False, False)
            status = status and sort_check_expr(cmd.inv, True, False)
        elif isinstance(cmd, ILCheckSystem):
            if not cmd.sys_symbol in context.defined_systems:
                print(f"Error: system `{cmd.sys_symbol}` undefined.")
                status = False
                continue

            system = context.defined_systems[cmd.sys_symbol]

            if len(system.input) != len(cmd.input):
                print(f"Error: input variables do not match target system ({system.symbol}).\n\t{system.input}\n\t{cmd.input}")
                status = False
                continue

            for i in range(0,len(system.input)):
                if system.input[i][1] != cmd.input[i][1]:
                    print(f"Error: sorts do not match in check-system (expected {system.input[i][1]}, got {cmd.input[i][1]})")
                    status = False
                    continue
                cmd.var_map[system.input[i][0]] = cmd.input[i][0]

            if len(system.output) != len(cmd.output):
                print(f"Error: input variables do not match target system ({system.symbol}).\n\t{system.output}\n\t{cmd.output}")
                status = False
                continue

            for i in range(0,len(system.output)):
                if system.output[i][1] != cmd.output[i][1]:
                    print(f"Error: sorts do not match in check-system (expected {system.output[i][1]}, got {cmd.output[i][1]})")
                    status = False
                    continue
                cmd.var_map[system.output[i][0]] = cmd.output[i][0]

            if len(system.local) != len(cmd.local):
                print(f"Error: input variables do not match target system ({system.symbol}).\n\t{system.input}\n\t{cmd.input}")
                status = False
                continue

            for i in range(0,len(system.local)):
                if system.local[i][1] != cmd.local[i][1]:
                    print(f"Error: sorts do not match in check-system (expected {system.local[i][1]}, got {cmd.local[i][1]})")
                    status = False
                    continue
                cmd.var_map[system.local[i][0]] = cmd.local[i][0]

            for expr in cmd.assumption.values():
                status = status and sort_check_expr(expr, False, True)

            for expr in cmd.reachable.values():
                status = status and sort_check_expr(expr, False, True)

            for expr in cmd.fairness.values():
                status = status and sort_check_expr(expr, False, True)

            for expr in cmd.current.values():
                status = status and sort_check_expr(expr, False, True)
        else:
            raise NotImplementedError

    return (status, context)