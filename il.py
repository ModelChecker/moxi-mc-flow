from __future__ import annotations
from typing import Any, Callable
from enum import Enum

from btor2 import Btor2InputVar, Btor2Node


il_operator_table = {
    "sext": []
}


class ILExpr():

    def __init__(self, c: list[ILExpr]) -> None:
        self._children = c

    def get_children(self) -> list[ILExpr]:
        return self._children


class ILVar(ILExpr):

    def __init__(self) -> None:
        super().__init__()


class ILInputVar(ILVar):

    def __init__(self) -> None:
        super().__init__()

    def to_btor2(srlf) -> Btor2Node:
        return Btor2InputVar()


class ILStateVar(ILVar):

    def __init__(self) -> None:
        super().__init__()


class ILOutputVar(ILVar):

    def __init__(self) -> None:
        super().__init__()


class ILApply(ILExpr):

    def __init__(self, op: ILOperator, args: list[ILExpr]) -> None:
        super().__init__()


class ILCommand():

    def __init__(self) -> None:
        pass


class ILDefineSystem(ILCommand):

    def __init__(self, attr: dict[str, str]) -> None:
        if "input" in attr:
            self.input = attr["input"]
        
        if "state" in attr:
            self.state = attr["state"]

        if "output" in attr:
            self.output = attr["output"]

        if "init" in attr:
            self.init = attr["init"]

        if "trans" in attr:
            self.trans = attr["trans"]
        
        if "inv" in attr:
            self.inv = attr["inv"]


class ILProgram():

    def __init__(self, cmds: list[ILCommand]) -> None:
        self.commands = cmds



def postorder_iterative(expr: ILExpr, func: Callable[[ILExpr], Any]) -> None:
    """Performs an iterative postorder traversal of 'expr', calling 'func' on each expr."""
    stack: list[tuple[bool, ILExpr]] = []
    visited: set[ILExpr] = set()

    stack.append((False, expr))

    while len(stack) > 0:
        cur = stack.pop()

        if cur[0]:
            func(cur[1])
            continue
        elif cur[1] in visited:
            continue

        visited.add(cur[1])
        stack.append((True, cur[1]))
        for child in cur[1].get_children():
            stack.append((False, child))
