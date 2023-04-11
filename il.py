from __future__ import annotations
from typing import Any, Callable
from enum import Enum

from numpy import extract

from btor2 import Btor2InputVar, Btor2Node


class ILSort():

    def __init__(self, symbol: str, sorts: list[ILSort], params: list[Any]) -> None:
        self.symbol = symbol
        self.sorts = sorts
        self.params = params


class ILExpr():

    def __init__(self) -> None:
        pass


class ILConstant(ILExpr):

    def __init__(self, sort: str, value: Any) -> None:
        super().__init__()


class ILVar(ILExpr):

    def __init__(self) -> None:
        super().__init__()


class ILInputVar(ILVar):

    def __init__(self) -> None:
        super().__init__()

    def to_btor2(self) -> Btor2Node:
        return Btor2InputVar()


class ILStateVar(ILVar):

    def __init__(self) -> None:
        super().__init__()


class ILOutputVar(ILVar):

    def __init__(self) -> None:
        super().__init__()


class ILApply(ILExpr):

    def __init__(self, op: str, args: list[ILExpr]) -> None:
        super().__init__()


class ILCommand():

    def __init__(self) -> None:
        pass


class ILDefineSystem(ILCommand):

    def __init__(self, attr: dict[str, Any]) -> None:
        if "input" in attr:
            self.input = attr["input"]
        else:
            self.input = []
        
        if "state" in attr:
            self.state = attr["state"]
        else:
            self.state = []

        if "output" in attr:
            self.output = attr["output"]
        else:
            self.output = []

        if "init" in attr:
            self.init = attr["init"]
        else:
            self.init = ILConstant("Bool", True)

        if "trans" in attr:
            self.trans = attr["trans"]
        else:
            self.trans = ILConstant("Bool", True)
        
        if "inv" in attr:
            self.inv = attr["inv"]
        else:
            self.inv = ILConstant("Bool", True)


class ILProgram():

    def __init__(self, cmds: list[ILCommand]) -> None:
        self.commands = cmds



def init_il_context() -> None:
    il_function_symbols = [
        "concat",
        "extract",
        "bvnot",
        "bvneg",
        "bvand",
        "bvor",
        "bvadd",
        "bvmul",
        "bvdiv",
        "bvudiv",
        "bvurem",
        "bvshl",
        "bvlshr",
        "bvult"
    ]

    # symbol -> (arity, num params)
    il_sort_symbols = {
        "Bool": (0,0),
        "BitVec": (0,1),
        "Array": (2,0),
    }



# def postorder_iterative(expr: ILExpr, func: Callable[[ILExpr], Any]) -> None:
#     """Performs an iterative postorder traversal of 'expr', calling 'func' on each expr."""
#     stack: list[tuple[bool, ILExpr]] = []
#     visited: set[ILExpr] = set()

#     stack.append((False, expr))

#     while len(stack) > 0:
#         cur = stack.pop()

#         if cur[0]:
#             func(cur[1])
#             continue
#         elif cur[1] in visited:
#             continue

#         visited.add(cur[1])
#         stack.append((True, cur[1]))
#         for child in cur[1].get_children():
#             stack.append((False, child))
