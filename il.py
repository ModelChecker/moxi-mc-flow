from __future__ import annotations
from typing import Any, Callable, NamedTuple, NewType
from enum import Enum

from btor2 import Btor2InputVar, Btor2Node, Btor2Sort, Btor2BitVec, Btor2Array

AttrDict = NewType("AttrDict", dict[str, Any])


class ILIdentifier(NamedTuple):
    """
    See section 3.3 of https://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2021-05-12.pdf.

    An identifier is a symbol and can be "indexed" with other symbols or numerals.
    """
    symbol: str
    indices: list[int|str]

    def __eq__(self, __value: object) -> bool:
        """Two ILIdentifiers are equal if they have the same symbol."""
        if isinstance(__value, ILIdentifier):
            return self.symbol == __value.symbol
        return False
        
        #     if self.symbol == __value.symbol:
        #         if len(self.indices) == len(__value.indices):
        #             for i in range(0, len(self.indices)):
        #                 if self.indices[i] != __value.indices[i]:
        #                     return False
        #             return True

        # return False


class ILSort():

    def __init__(self, identifier: ILIdentifier, sorts: list[ILSort]) -> None:
        self.identifier = identifier
        self.sorts = sorts

    def to_btor2(self) -> Btor2Sort:
        if self.identifier == "BitVec" and isinstance(self.identifier.indices[0], int):
            return Btor2BitVec(self.identifier.indices[0])
        elif self.identifier == "Array":
            return Btor2Array(self.sorts[0].to_btor2(), self.sorts[1].to_btor2())
        else:
            raise NotImplementedError


class ILExpr():

    def __init__(self) -> None:
        pass


class ILConstant(ILExpr):

    def __init__(self, sort: str, value: Any) -> None:
        super().__init__()
        self.sort = sort
        self.value = value


class ILVar(ILExpr):

    def __init__(self, symbol: str, sort: ILSort) -> None:
        super().__init__()
        self.symbol = symbol
        self.sort = sort


class ILInputVar(ILVar):

    def __init__(self, symbol: str, sort: ILSort) -> None:
        super().__init__(symbol, sort)

    def to_btor2(self) -> Btor2Node:
        return Btor2InputVar(self.sort.to_btor2())


class ILStateVar(ILVar):

    def __init__(self, symbol: str, sort: ILSort) -> None:
        super().__init__(symbol, sort)


class ILOutputVar(ILVar):

    def __init__(self, symbol: str, sort: ILSort) -> None:
        super().__init__(symbol, sort)


class ILApply(ILExpr):

    def __init__(self, op: str, args: list[ILExpr]) -> None:
        super().__init__()


class ILSystem():

    def __init__(
        self, 
        input: list[ILInputVar], 
        state: list[ILStateVar], 
        output: list[ILOutputVar], 
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


class ILDefineSort(ILCommand):

    def __init__(self, symbol: str, arity: int) -> None:
        super().__init__()
        self.symbol = symbol
        self.arity = arity


class ILDefineSystem(ILCommand):

    def __init__(
        self, 
        symbol: str, 
        input: list[ILInputVar], 
        state: list[ILStateVar], 
        output: list[ILOutputVar], 
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
        # Maps sort symbol to 
        self.sort_table: dict[ILIdentifier, int] = {
            ILIdentifier("Bool", []): 0,
            ILIdentifier("BitVec", []): 0,
            ILIdentifier("Array", []): 2,
        }

        # If symbol points to "None", then it's a built-in function (defined in the Theory)
        self.function_table: dict[str, None|ILExpr] = {
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

    def __init__(self, cmds: list[ILCommand]) -> None:
        self.context = ILContext()
        self.commands = cmds

    def execute(self) -> None:
        for cmd in self.commands:
            if isinstance(cmd, ILDefineSort):
                self.context.sort_table[ILIdentifier(cmd.symbol, [])] = cmd.arity
            elif isinstance(cmd, ILDefineSystem):
                self.context.system_table[cmd.symbol] = ILSystem(
                    cmd.input,
                    cmd.state,
                    cmd.output,
                    cmd.init,
                    cmd.trans,
                    cmd.inv
                )

