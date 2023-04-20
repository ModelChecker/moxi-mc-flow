from __future__ import annotations
from typing import Any, Callable, NamedTuple, NewType, Dict, List
from enum import Enum

from btor2 import *


class ILIdentifier(NamedTuple):
    """
    See section 3.3 of https://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2021-05-12.pdf.

    An identifier is a symbol and can be "indexed" with other symbols or numerals.
    """
    symbol: str
    indices: List[int|str]

    def __eq__(self, __value: object) -> bool:
        """Two ILIdentifiers are equal if they have the same symbol."""
        if isinstance(__value, ILIdentifier):
            return self.symbol == __value.symbol
        return False

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

IL_NO_SORT = ILSort(ILIdentifier("", []), [])
IL_BOOL_SORT = ILSort(ILIdentifier("Bool", []), [])


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


class ILStateVar(ILVar):

    def __init__(self, symbol: str, sort: ILSort, prime: bool) -> None:
        super().__init__(symbol, sort, prime)


class ILOutputVar(ILVar):

    def __init__(self, symbol: str, sort: ILSort, prime: bool) -> None:
        super().__init__(symbol, sort, prime)


class ILApply(ILExpr):

    def __init__(self, op: str, args: List[ILExpr]) -> None:
        super().__init__(args)
        self.symbol = op


class ILSystem():

    def __init__(
        self, 
        input: List[ILInputVar], 
        state: List[ILStateVar], 
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
        state: List[ILStateVar], 
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


class ILContext():

    def __init__(self) -> None:
        # Maps sort symbol to arity
        # self.sort_table: Dict[ILIdentifier, int] = {
        #     ILIdentifier("Bool", []): 0,
        #     ILIdentifier("BitVec", []): 0,
        #     ILIdentifier("Array", []): 2,
        # }

        # If symbol points to "None", then it's a built-in function (defined in the Theory)
        self.function_table: Dict[str, None|ILExpr] = {
            "concat": None,
            "extract": None,
            "bvnot": None,
            "bvneg": None,
            "bvand": None,
            "bvor": None,
            "bvadd": None,
            "bvmul": None,
            "bvdiv": None,
            "bvudiv": None,
            "bvurem": None,
            "bvshl": None,
            "bvlshr": None,
            "bvult": None
        }

        self.system_table = {}


class ILProgram():

    def __init__(self, cmds: List[ILCommand]) -> None:
        self.context = ILContext()
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
    visited: List[ILExpr] = []

    stack.append((False, expr))

    while len(stack) > 0:
        cur = stack.pop()

        if cur[0]:
            func(cur[1])
            continue
        elif cur[1] in visited:
            continue

        visited.append(cur[1])
        stack.append((True, cur[1]))
        for child in cur[1].children:
            stack.append((False, child))