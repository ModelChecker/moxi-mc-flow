"""
https://fmv.jku.at/papers/NiemetzPreinerWolfBiere-CAV18.pdf
"""
from __future__ import annotations
from collections import deque
from enum import Enum
import os
from pathlib import Path
from typing import Any, Optional
import pickle

from src import util

FILE_NAME = Path(__file__).name

EMPTY_ARGS = (None, None, None)


class BtorOperator(Enum):
    # indexed (also unary)
    SEXT = 0
    UEXT = 1
    SLICE = 2

    # unary
    NOT = 100
    INC = 101
    DEC = 102
    NEG = 103
    REDAND = 104
    REDOR = 105
    REDXOR = 106

    # binary
    IFF = 200
    IMPLIES = 201
    EQ = 202
    NEQ = 203
    SGT = 204
    UGT = 205
    SGTE = 206
    UGTE = 207
    SLT = 208
    ULT = 209
    SLTE = 210
    ULTE = 211
    AND = 212
    NAND = 213
    NOR = 214
    OR = 215
    XNOR = 216
    XOR = 217
    ROL = 218
    ROR = 219
    SLL = 220
    SRA = 221
    SRL = 222
    ADD = 223
    MUL = 224
    SDIV = 225
    UDIV = 226
    SMOD = 227
    SREM = 228
    UREM = 229
    SUB = 230
    SADDO = 231
    UADDO = 232
    SDIVO = 233
    UDIVO = 234
    SMULO = 235
    UMULO = 236
    SSUBO = 237
    USUBO = 238
    CONCAT = 239
    READ = 240

    # ternary
    ITE = 300
    WRITE = 301

    def id(self) -> str:
        """Returns name of operator as used in the Btor syntax."""
        return f"{self.name.lower()}"

    def is_indexed(self) -> bool:
        return self.value >= 0 and self.value < 100

    def is_unary(self) -> bool:
        return self.value >= 0 and self.value < 200

    def is_binary(self) -> bool:
        return self.value >= 200 and self.value < 300

    def is_ternary(self) -> bool:
        return self.value >= 300 and self.value < 400


class BtorNode:
    def __init__(self):
        self.nid = -1
        self.comment = ""

    def set_comment(self, s: str):
        self.comment = f" ; {s}"

    def set_comment_no_space(self, s: str):
        self.comment = f"; {s}"

    def __str__(self) -> str:
        return f"{self.comment}"


class BtorSort(BtorNode):
    def __init__(self):
        super().__init__()


class BtorBitVec(BtorSort):
    def __init__(self, len: int):
        super().__init__()
        self.length = len
        self.symbol = "bitvec"

    def __repr__(self) -> str:
        return f"({self.nid} sort {self.symbol} {self.length})"

    def __str__(self) -> str:
        return f"{self.nid} sort {self.symbol} {self.length}{self.comment}"

    def __eq__(self, __value: object) -> bool:
        if not isinstance(__value, BtorBitVec):
            return False
        return self.length == __value.length

    def __hash__(self) -> int:
        return self.length


class BtorArray(BtorSort):
    def __init__(self, domain: BtorSort, range: BtorSort):
        super().__init__()
        self.domain = domain
        self.range = range
        self.symbol = "array"

    def __repr__(self) -> str:
        return f"({self.nid} sort {self.symbol} {repr(self.domain)} {repr(self.range)})"

    def __str__(self) -> str:
        return f"{self.nid} sort {self.symbol} {self.domain.nid} {self.range.nid}{self.comment}"

    def __eq__(self, __value: object) -> bool:
        if isinstance(__value, BtorArray):
            return self.domain == __value.domain and self.range == __value.range
        else:
            return False

    def __hash__(self) -> int:
        return hash((self.domain, self.range))


class BtorExpr(BtorNode):
    def __init__(self, c: BtorArgs):
        super().__init__()
        self.children = c


class BtorVar(BtorExpr):
    def __init__(self, sort: BtorSort, symbol: str = ""):
        super().__init__(EMPTY_ARGS)
        self.sort: BtorSort = sort
        self.symbol = symbol
        self.var_index: int = 0  # used to refer to vars in witness

    def with_no_suffix(self) -> str:
        return (
            ((str(self.symbol)).removesuffix(".init")).removesuffix(".cur")
        ).removesuffix("next")


class BtorInputVar(BtorVar):
    def __init__(self, sort: BtorSort, symbol: str = ""):
        super().__init__(sort, symbol)

    def __str__(self) -> str:
        return f"{self.nid} input {self.sort.nid} {self.symbol}{self.comment}"

    def __eq__(self, __o: object) -> bool:
        if not isinstance(__o, BtorInputVar):
            return False
        return self.sort == __o.sort and self.symbol == __o.symbol

    def __hash__(self) -> int:
        return hash((self.sort, self.symbol))


class BtorStateVar(BtorVar):
    def __init__(self, sort: BtorSort, symbol: str = ""):
        super().__init__(sort, symbol)

    def __repr__(self) -> str:
        return f"({self.nid} state {self.symbol})"

    def __str__(self) -> str:
        return f"{self.nid} state {self.sort.nid} {self.symbol}{self.comment}"

    def __eq__(self, __o: object) -> bool:
        if not isinstance(__o, BtorStateVar):
            return False
        return self.sort == __o.sort and self.symbol == __o.symbol

    def __hash__(self) -> int:
        return hash((self.sort, self.symbol))


class BtorConst(BtorExpr):
    def __init__(self, sort: BtorSort, val: Any):
        super().__init__(EMPTY_ARGS)
        self.sort = sort
        self.value = val

    def __str__(self) -> str:
        return f"{self.nid} constd {self.sort.nid} {int(self.value)}{self.comment}"

    def __eq__(self, __o: object) -> bool:
        if not isinstance(__o, BtorConst):
            return False
        return self.sort == __o.sort and self.value == __o.value

    def __hash__(self) -> int:
        return hash((self.sort, self.value))


# BTOR2 operators have only 1, 2, or 3 arguments
BtorArgs = tuple[Optional[BtorExpr], Optional[BtorExpr], Optional[BtorExpr]]


class BtorApply(BtorExpr):
    def __init__(
        self,
        sort: BtorSort,
        op: BtorOperator,
        indices: tuple[Optional[int], Optional[int]],
        args: BtorArgs,
    ) -> None:
        super().__init__(args)
        self.indices = indices
        self.sort = sort
        self.operator = op

    def __repr__(self) -> str:
        s = f"({id(self)} "
        s += f"{self.nid} "
        s += f"{self.operator.name.lower()} "
        s += f"{' '.join([repr(c) for c in self.children if c] + [str(i) for i in self.indices if i is not None])})"
        return s

    def __str__(self) -> str:
        s = f"{self.nid} "
        s += f"{self.operator.name.lower()} "
        s += f"{self.sort.nid} "
        s += f"{' '.join([str(c.nid) for c in self.children if c] + [str(i) for i in self.indices if i is not None])}"
        s += f"{self.comment}"
        return s

    def __eq__(self, __o: object) -> bool:
        return id(self) == id(__o)

    def __hash__(self) -> int:
        return hash(id(self))


def eq_btor(e1: BtorExpr, e2: object) -> bool:
    """Returns `True` if `e1` and `e2` are syntactically equivalent."""
    if not isinstance(e2, BtorExpr):
        return False

    try:
        for c1, c2 in zip(preorder_btor(e1), preorder_btor(e2), strict=True):
            if isinstance(c1, BtorVar) and isinstance(c2, BtorVar):
                if c1.symbol != c2.symbol:
                    return False
            elif isinstance(c1, BtorConst) and isinstance(c2, BtorConst):
                if c1.sort != c2.sort:
                    return False
                elif c1.value != c2.value:
                    return False
            elif isinstance(c1, BtorApply) and isinstance(c2, BtorApply):
                if c1.operator != c2.operator:
                    return False
                elif c1.sort != c2.sort:
                    return False
            else:
                return False
        return True
    except ValueError:
        return False


def hash_btor(expr: BtorExpr) -> int:
    """Returns a hash for `expr`. For `BtorApply` objects, uses the 30 closest nodes in the tree to perform the hash."""
    if isinstance(expr, BtorVar):
        return hash((expr.sort, expr.symbol))
    elif isinstance(expr, BtorConst):
        return hash((expr.sort, expr.value))
    elif isinstance(expr, BtorApply):
        h, cnt = 0, 0

        for subexpr in preorder_btor(expr):
            if isinstance(expr, BtorVar):
                h = hash((h, expr.sort, expr.symbol))
            elif isinstance(expr, BtorConst):
                h = hash((h, expr.sort, expr.value))
            if isinstance(subexpr, BtorApply):
                h = hash((h, subexpr.sort, subexpr.operator))

            if cnt > 30:
                return h
            cnt += 1

        return h

    raise NotImplementedError(f"Hash not implemented for {type(expr)}")


class BtorConstraint(BtorNode):
    def __init__(self, expr: BtorNode):
        super().__init__()
        self.expr = expr

    def __str__(self) -> str:
        return f"{self.nid} constraint {self.expr.nid}{self.comment}"

    def __eq__(self, __o: object) -> bool:
        if not isinstance(__o, BtorConstraint):
            return False
        return self.expr == __o.expr

    def __hash__(self) -> int:
        return hash((type(self), self.expr))


class BtorInit(BtorNode):
    def __init__(self, state: BtorStateVar, expr: BtorNode):
        super().__init__()
        self.state = state
        self.expr = expr

    def __str__(self) -> str:
        return f"{self.nid} init {self.state.sort.nid} {self.state.nid} {self.expr.nid}{self.comment}"

    def __eq__(self, __o: object) -> bool:
        if not isinstance(__o, BtorInit):
            return False
        return self.state == __o.state and self.expr == __o.expr

    def __hash__(self) -> int:
        return hash((self.state, self.expr))


class BtorNext(BtorNode):
    def __init__(self, state: BtorStateVar, expr: BtorNode):
        super().__init__()
        self.state = state
        self.expr = expr

    def __str__(self) -> str:
        return f"{self.nid} next {self.state.sort.nid} {self.state.nid} {self.expr.nid}{self.comment}"

    def __eq__(self, __o: object) -> bool:
        if not isinstance(__o, BtorNext):
            return False
        return self.state == __o.state and self.expr == __o.expr

    def __hash__(self) -> int:
        return hash((self.state, self.expr))


class BtorBad(BtorNode):
    def __init__(self, expr: BtorNode):
        super().__init__()
        self.expr = expr

    def __str__(self) -> str:
        return f"{self.nid} bad {self.expr.nid}{self.comment}"


class BtorFair(BtorNode):
    def __init__(self, expr: BtorNode):
        super().__init__()
        self.expr = expr

    def __str__(self) -> str:
        return f"{self.nid} fair {self.expr.nid}{self.comment}"


class BtorProgram:
    def __init__(self, nodes: list[BtorNode]):
        self.nodes = nodes

    def __str__(self) -> str:
        return "\n".join([str(n) for n in self.nodes]) + "\n"


# The elements of a BtorProgramSet represent translated check-system commands,
# where each dict maps the query symbol to the respective program
BtorProgramSet = list[tuple[str, dict[str, BtorProgram]]]


operator_table: dict[BtorOperator, tuple[list[type], type]] = {
    BtorOperator.SEXT: ([BtorBitVec], BtorBitVec)
}


def flatten_btor2_expr(expr: BtorExpr) -> list[BtorExpr]:
    out: list[BtorExpr] = []
    for subexpr in postorder_btor(expr):
        out.append(subexpr)
    return out


def postorder_btor(expr: BtorExpr):
    """Perform an iterative postorder traversal of `expr`."""
    stack: list[tuple[bool, BtorExpr]] = []
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

        for child in [c for c in cur.children if c]:
            stack.append((False, child))


def preorder_btor(expr: BtorExpr):
    """Perform an iterative preorder traversal of `expr`."""
    queue: deque[BtorExpr] = deque()
    visited: set[int] = set()

    queue.append(expr)

    while len(queue) > 0:
        cur = queue.popleft()

        if id(cur) in visited:
            continue
        yield cur

        visited.add(id(cur))

        for child in [c for c in cur.children if c]:
            queue.append(child)


def assign_nids(program: list[BtorNode]) -> list[BtorNode]:
    btor2_nids: dict[BtorNode, int] = {}
    cur_nid = 1

    reduced_program: list[BtorNode] = []
    for node in program:
        if str(node)[0] == ";":
            reduced_program.append(node)
        elif node not in btor2_nids:
            node.nid = cur_nid
            btor2_nids[node] = cur_nid
            cur_nid += 1
            reduced_program.append(node)
        else:
            node.nid = btor2_nids[node]

    return reduced_program


def write_btor2_program_set(
    program_set: BtorProgramSet, output_path: Path, do_pickle: bool, do_overwrite: bool
) -> bool:
    status = util.cleandir(output_path, do_overwrite)
    if not status:
        return False

    program_index: dict[str, int] = {}
    for symbol, programs in program_set:
        if symbol not in program_index:
            program_index[symbol] = 1

        program_output_path = output_path / f"{symbol}.{program_index[symbol]}"

        program_index[symbol] += 1

        os.mkdir(program_output_path)

        for query_symbol, program in programs.items():
            output_file_path = program_output_path / f"{query_symbol}.btor2"

            with open(str(output_file_path), "w") as f:
                f.write(str(program))

            if do_pickle:
                with open(output_file_path.with_suffix(".btor2.pickle"), "wb") as f:
                    pickle.dump(program, f)

    return True
