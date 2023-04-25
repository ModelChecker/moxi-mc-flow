from __future__ import annotations
from ast import Call
from typing import Any, Callable, NamedTuple, NewType, Dict, List, NoReturn
from enum import Enum

from numpy import indices
from traitlets import Bool, TraitType

from btor2 import *

class ILIdentifier(NamedTuple):
    """
    An identifier is a symbol and can be "indexed" with numerals. As opposed to SMT-LIB2, we restrict indices to numerals and not symbols and numerals.

    See section 3.3 of https://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2021-05-12.pdf.
    """
    symbol: str
    indices: List[int]

    def __eq__(self, __value: object) -> bool:
        """Two ILIdentifiers are equal if they have the same symbol."""
        if isinstance(__value, ILIdentifier):
            return self.symbol == __value.symbol
        return False

    def __hash__(self) -> int:
        return hash(self.symbol)

    def __str__(self) -> str:
        s = f"({self.symbol} "
        for index in self.indices:
            s += f"{index} "
        return s[:-1]+")"


class ILSort():

    def __init__(self, identifier: ILIdentifier, sorts: List[ILSort]) -> None:
        self.identifier = identifier
        self.sorts = sorts

    def __eq__(self, __value: object) -> bool:
        return isinstance(__value, ILSort) and self.identifier == __value.identifier
    
    def __hash__(self) -> int:
        return hash(self.identifier.symbol)
    
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
    """The bit vector sort is defined as an identifier with the symbol 'BitVec' and is indexed with a single numeral."""
    if sort.identifier.symbol != "BitVec" or len(sort.sorts) != 0 or len(sort.identifier.indices) != 1:
        return False
    return True


class ILExpr():

    def __init__(self, c: List[ILExpr]) -> None:
        self.children = c
        self.sort = IL_NO_SORT
        
    def __hash__(self) -> int:
        return id(self)


class ILConstant(ILExpr):

    def __init__(self, sort: ILSort, value: Any) -> None:
        super().__init__([])
        self.sort = sort
        self.value = value


class ILVar(ILExpr):

    def __init__(self, symbol: str, sort: ILSort, prime: bool) -> None:
        super().__init__([])
        self.symbol = symbol
        self.sort = sort
        self.prime = prime

    def __eq__(self, __value: object) -> bool:
        if type(self) == type(__value) and isinstance(__value, ILVar):
            return self.symbol == __value.symbol and self.prime == __value.prime
        return False


class ILInputVar(ILVar):

    def __init__(self, symbol: str, sort: ILSort, prime: bool) -> None:
        super().__init__(symbol, sort, prime)


class ILLocalVar(ILVar):

    def __init__(self, symbol: str, sort: ILSort, prime: bool) -> None:
        super().__init__(symbol, sort, prime)


class ILOutputVar(ILVar):

    def __init__(self, symbol: str, sort: ILSort, prime: bool) -> None:
        super().__init__(symbol, sort, prime)


class ILApply(ILExpr):

    def __init__(self, id: ILIdentifier, args: List[ILExpr]) -> None:
        super().__init__(args)
        self.function = id


class ILSystem():

    def __init__(
        self, 
        input: List[ILInputVar], 
        state: List[ILLocalVar], 
        output: List[ILOutputVar], 
        init: ILExpr, 
        trans: ILExpr, 
        inv: ILExpr
    ) -> None:
        self.input = input
        self.state = state
        self.output = output
        self.init = init
        self.trans = trans
        self.inv = inv


class ILCommand():

    def __init__(self) -> None:
        pass


class ILDeclareSort(ILCommand):

    def __init__(self, symbol: str, arity: int) -> None:
        super().__init__()
        self.symbol = symbol
        self.arity = arity


class ILDefineSort(ILCommand):

    def __init__(self, symbol: str, arity: int) -> None:
        super().__init__()
        self.symbol = symbol
        self.arity = arity


class ILDeclareConst(ILCommand):

    def __init__(self, symbol: str, sort: ILSort) -> None:
        super().__init__()
        self.symbol = symbol
        self.sort = sort


class ILDefineSystem(ILCommand):

    def __init__(
        self, 
        symbol: str, 
        input: Dict[str, ILSort], 
        state: List[ILLocalVar], 
        output: List[ILOutputVar], 
        init: ILExpr, 
        trans: ILExpr, 
        inv: ILExpr
    ) -> None:
        self.symbol = symbol
        self.input = input
        self.state = state
        self.output = output
        self.init = init
        self.trans = trans
        self.inv = inv


class ILCheckSystem():

    def __init__(self) -> None:
        pass


class ILLogic(NamedTuple):
        name: str
        functions: set[str]
        sort_check: Callable[[ILApply], bool]

def sort_check_apply_bv(node: ILApply) -> bool:
    """True if node corresponds to function signature in SMT-LIB2 QF_BV logic."""
    function = node.function

    if function.symbol == "extract":
        # ((_ extract i j) (_ BitVec m) (_ BitVec n))
        if len(function.indices) == 2:
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
    elif function.symbol == "bvand":
        # (bvand (_ BitVec m) (_ BitVec m) (_ BitVec m))
        return True

    return False

FUNCTIONS_BV = {"extract", "bvnot"}
QF_BV = ILLogic("QF_BV", FUNCTIONS_BV, sort_check_apply_bv)


class ILContext():

    def __init__(self) -> None:
        self.declared_sorts: dict[ILSort, int] = {}
        self.defined_sorts: dict[ILSort, tuple[list[ILSort], ILSort]] = {}
        self.declared_functions: set[str] = set()
        self.defined_functions: dict[str, tuple[list[ILSort], ILSort]] = {}
        self.defined_systems: dict[str, ILSystem] = {}

        # for now, assume QF_BV logic
        self.logic = QF_BV

        # context stack of systems
        self.system_context: list[ILSystem] = []


class ILProgram():

    def __init__(self, cmds: List[ILCommand]) -> None:
        self.commands = cmds

    # def execute(self) -> None:
    #     for cmd in self.commands:
    #         if isinstance(cmd, ILDefineSort):
    #             self.context.sort_table[ILIdentifier(cmd.symbol, [])] = cmd.arity
    #         elif isinstance(cmd, ILDefineSystem):
    #             self.context.system_table[cmd.symbol] = ILSystem(
    #                 cmd.input,
    #                 cmd.state,
    #                 cmd.output,
    #                 cmd.init,
    #                 cmd.trans,
    #                 cmd.inv
    #             )


def postorder_iterative(expr: ILExpr, func: Callable[[ILExpr], Any]) -> None:
    """Perform an iterative postorder traversal of node, calling func on each node."""
    stack: List[tuple[bool, ILExpr]] = []
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


def sort_check(program: ILProgram) -> bool:
    context: ILContext = ILContext()
    status: bool = True

    def sort_check_expr(node: ILExpr) -> bool:
        nonlocal context

        if isinstance(node, ILConstant):
            pass
        elif isinstance(node, ILVar):
            pass
        elif isinstance(node, ILApply):
            arg_sorts: list[ILSort] = []
            return_sort: ILSort = IL_NO_SORT

            if node.function.symbol in context.logic.functions:
                for arg in node.children:
                    sort_check_expr(arg)
                return context.logic.sort_check(node)
            elif node.function.symbol in context.defined_functions:
                (arg_sorts, return_sort) = context.defined_functions[node.function.symbol]

                if len(arg_sorts) == len(node.children):
                    for i in range(0, len(arg_sorts)):
                        sort_check_expr(node.children[i])

                        if arg_sorts[i] != node.children[i].sort:
                            return False
                else:
                    return False
            else:
                return False

            node.sort = return_sort
            return True

        return False
    # end sort_check_expr

    for command in program.commands:
        if isinstance(command, ILDeclareSort):
            pass
        elif isinstance(command, ILDefineSort):
            pass
        elif isinstance(command, ILDeclareConst):
            pass
        elif isinstance(command, ILDefineSystem):
            pass
        elif isinstance(command, ILCheckSystem):
            pass
        else:
            raise NotImplementedError

    return status