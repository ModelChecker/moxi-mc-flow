"""
https://fmv.jku.at/papers/NiemetzPreinerWolfBiere-CAV18.pdf
"""
from __future__ import annotations
from enum import Enum
from typing import Any, Callable, Optional

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


class BtorNode():

    def __init__(self):
        self.nid = -1
        self.comment = ""

    def set_comment(self, s: str):
        self.comment = f" ; {s}"

    def __str__(self) -> str:
        return f"{self.nid}{self.comment}"


class BtorSort(BtorNode):

    def __init__(self):
        super().__init__()


class BtorBitVec(BtorSort):

    def __init__(self, len: int):
        super().__init__()
        self.length = len
        self.name = "bitvec"
        
    def __repr__(self) -> str:
        return f"({self.nid} sort {self.name} {self.length})"

    def __str__(self) -> str:
        return f"{self.nid} sort {self.name} {self.length}{self.comment}"
    
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
        self.name = "array"
        
    def __repr__(self) -> str:
        return f"({self.nid} sort {self.name} {repr(self.domain)} {repr(self.range)})"

    def __str__(self) -> str:
        return f"{self.nid} sort {self.name} {self.domain.nid} {self.range.nid}{self.comment}"
    
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

# BTOR2 operators have only 1, 2, or 3 arguments
BtorArgs = tuple[Optional[BtorExpr], Optional[BtorExpr], Optional[BtorExpr]]

class BtorVar(BtorExpr):

    def __init__(self, sort: BtorSort, name: str = ""):
        super().__init__(EMPTY_ARGS)
        self.sort: BtorSort = sort
        self.name = name
        self.var_index: int = 0  # used to refer to vars in witness

    def __eq__(self, __o: object) -> bool:
        if not isinstance(__o, BtorVar):
            return False
        return self.name == __o.name

    def __hash__(self) -> int:
        return hash((self.sort, self.name))


class BtorInputVar(BtorVar):

    def __init__(self, sort: BtorSort, name: str = ""):
        super().__init__(sort, name)

    def __str__(self) -> str:
        return f"{self.nid} input {self.sort.nid} {self.name}{self.comment}"


class BtorStateVar(BtorVar):

    def __init__(self, sort: BtorSort, name: str = ""):
        super().__init__(sort, name)

    def __repr__(self) -> str:
        return f"({self.nid} state {self.name})"

    def __str__(self) -> str:
        return f"{self.nid} state {self.sort.nid} {self.name}{self.comment}"


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


class BtorApply(BtorExpr):

    def __init__(self, sort: BtorSort, op: BtorOperator, args: BtorArgs):
        super().__init__(args)
        self.sort = sort
        self.operator = op

    def __repr__(self) -> str:
        return f"({id(self)} {self.nid} {self.operator.name.lower()} {' '.join([repr(c) for c in self.children if c])})"

    def __str__(self) -> str:
        return f"{self.nid} {self.operator.name.lower()} {self.sort.nid} {' '.join([str(c.nid) for c in self.children if c])}{self.comment}"

    def __eq__(self, __o: object) -> bool:
        if not isinstance(__o, BtorApply):
            return False

        if not self.operator == __o.operator:
            return False
        
        if not self.sort == __o.sort:
            return False

        if not len(self.children) == len(__o.children):
            return False

        for i in range(0, len(self.children)-1):
            if self.children[i] != __o.children[i]:
                return False
        
        return True

    def __hash__(self) -> int:
        return hash((self.operator, self.sort, self.children))


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


class BtorProgram():

    def __init__(self, sorts: set[BtorSort], instr: list[BtorExpr]):
        self.sorts = sorts
        self.instructions = instr

    def __str__(self) -> str:
        s: str  = ""
        for sort in self.sorts:
            s += f"{sort}\n"
        for instruction in self.instructions:
            s += f"{instruction}\n"
        return s[:-1] # delete last newline and return
    

operator_table: dict[BtorOperator, tuple[list[type], type]] = {
    BtorOperator.SEXT: ([BtorBitVec], BtorBitVec)
}


def postorder_iterative_btor2(expr: BtorExpr, func: Callable[[BtorExpr], Any]):
    """Perform an iterative postorder traversal of node, calling func on each node."""
    stack: list[tuple[bool, BtorExpr]] = []
    visited: set[int] = set()

    stack.append((False, expr))

    while len(stack) > 0:
        (seen, cur) = stack.pop()

        if seen:
            func(cur)
            continue
        elif cur in visited:
            continue

        visited.add(id(cur))
        stack.append((True, cur))

        for child in [c for c in cur.children if c]:
            stack.append((False, child))