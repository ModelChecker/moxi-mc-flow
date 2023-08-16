"""
https://fmv.jku.at/papers/NiemetzPreinerWolfBiere-CAV18.pdf
"""
from __future__ import annotations
from enum import Enum
from typing import Any, Callable, Optional

EMPTY_ARGS = (None, None, None)

class Btor2Operator(Enum):
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
        """Returns name of operator as used in the Btor2 syntax."""
        return f"{self.name.lower()}"
    
    def is_indexed(self) -> bool:
        return self.value >= 0 and self.value < 100
    
    def is_unary(self) -> bool:
        return self.value >= 0 and self.value < 200

    def is_binary(self) -> bool:
        return self.value >= 200 and self.value < 300

    def is_ternary(self) -> bool:
        return self.value >= 300 and self.value < 400


class Btor2Node():

    def __init__(self):
        self.nid = -1
        self.comment = ""

    def set_comment(self, s: str):
        self.comment = f" ; {s}"

    def __str__(self) -> str:
        return f"{self.nid}{self.comment}"

    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Btor2Node) and self.__str__() == __o.__str__()

    def __hash__(self) -> int:
        return self.nid


class Btor2Sort(Btor2Node):

    def __init__(self):
        super().__init__()


class Btor2BitVec(Btor2Sort):

    def __init__(self, len: int):
        super().__init__()
        self.length = len
        self.name = "bitvec"
        
    def __str__(self) -> str:
        return f"{self.nid} sort {self.name} {self.length}{self.comment}"
    
    def __eq__(self, __value: object) -> bool:
        if not isinstance(__value, Btor2BitVec):
            return False
        return self.length == __value.length

    def __hash__(self) -> int:
        return self.length


class Btor2Array(Btor2Sort):

    def __init__(self, domain: Btor2Sort, range: Btor2Sort):
        super().__init__()
        self.domain = domain
        self.range = range
        self.name = "array"

    def __str__(self) -> str:
        return f"{self.nid} sort {self.name} {self.domain.nid} {self.range.nid}{self.comment}"
    
    def __eq__(self, __value: object) -> bool:
        if isinstance(__value, Btor2Array):
            return self.domain == __value.domain and self.range == __value.range
        else:
            return False

    def __hash__(self) -> int:
        """TODO"""
        if isinstance(self.domain, Btor2BitVec):
            domain_hash = hash(self.domain)
        else:
            pass

        if isinstance(self.range, Btor2BitVec):
            range_hash = hash(self.range)
        else:
            pass

        return 0


class Btor2Expr(Btor2Node):

    def __init__(self, c: Btor2Args):
        super().__init__()
        self.children = c

# BTOR2 operators have only 1, 2, or 3 arguments
Btor2Args = tuple[Optional[Btor2Expr], Optional[Btor2Expr], Optional[Btor2Expr]]

class Btor2Var(Btor2Expr):

    def __init__(self, sort: Btor2Sort, name: str = ""):
        super().__init__(EMPTY_ARGS)
        self.sort: Btor2Sort = sort
        self.name = name

    def __eq__(self, __o: object) -> bool:
        if not isinstance(__o, Btor2Var):
            return False
        return self.name == __o.name

    def __hash__(self) -> int:
        return hash(self.name)


class Btor2InputVar(Btor2Var):

    def __init__(self, sort: Btor2Sort, name: str = ""):
        super().__init__(sort, name)

    def __str__(self) -> str:
        return f"{self.nid} input {self.sort.nid} {self.name}{self.comment}"


class Btor2StateVar(Btor2Var):

    def __init__(self, sort: Btor2Sort, name: str = ""):
        super().__init__(sort, name)

    def __str__(self) -> str:
        return f"{self.nid} state {self.sort.nid} {self.name}{self.comment}"


class Btor2Const(Btor2Expr):

    def __init__(self, sort: Btor2Sort, val: Any):
        super().__init__(EMPTY_ARGS)
        self.sort = sort
        self.value = val

    def __str__(self) -> str:
        return f"{self.nid} constd {self.sort.nid} {int(self.value)}{self.comment}"
    
    def __eq__(self, __o: object) -> bool:
        if not isinstance(__o, Btor2Const):
            return False
        return self.sort == __o.sort and self.value == __o.value

    def __hash__(self) -> int:
        return hash((self.sort, self.value))


class Btor2Apply(Btor2Expr):

    def __init__(self, sort: Btor2Sort, op: Btor2Operator, args: Btor2Args):
        super().__init__(args)
        self.sort = sort
        self.operator = op

    def __str__(self) -> str:
        s = f"{self.nid} {self.operator.name.lower()} {self.sort.nid} "
        for arg in [c for c in self.children if c]:
            s += f"{arg.nid} "
        return f"{s[:-1]}{self.comment}"

    def __eq__(self, __o: object) -> bool:
        if not isinstance(__o, Btor2Apply):
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


class Btor2Constraint(Btor2Node):

    def __init__(self, expr: Btor2Node):
        super().__init__()
        self.expr = expr

    def __str__(self) -> str:
        return f"{self.nid} constraint {self.expr.nid}{self.comment}"
    
    def __eq__(self, __o: object) -> bool:
        if not isinstance(__o, Btor2Constraint):
            return False
        return self.expr == __o.expr
    
    def __hash__(self) -> int:
        return hash((type(self), self.expr))


class Btor2Init(Btor2Node):

    def __init__(self, state: Btor2StateVar, expr: Btor2Node):
        super().__init__()
        self.state = state
        self.expr = expr

    def __str__(self) -> str:
        return f"{self.nid} init {self.state.sort.nid} {self.state.nid} {self.expr.nid}{self.comment}"

    def __eq__(self, __o: object) -> bool:
        if not isinstance(__o, Btor2Init):
            return False
        return self.state == __o.state and self.expr == __o.expr

    def __hash__(self) -> int:
        return hash((self.state, self.expr))


class Btor2Next(Btor2Node):

    def __init__(self, state: Btor2StateVar, expr: Btor2Node):
        super().__init__()
        self.state = state
        self.expr = expr

    def __str__(self) -> str:
        return f"{self.nid} next {self.state.sort.nid} {self.state.nid} {self.expr.nid}{self.comment}"

    def __eq__(self, __o: object) -> bool:
        if not isinstance(__o, Btor2Next):
            return False
        return self.state == __o.state and self.expr == __o.expr

    def __hash__(self) -> int:
        return hash((self.state, self.expr))


class Btor2Bad(Btor2Node):

    def __init__(self, expr: Btor2Node):
        super().__init__()
        self.expr = expr

    def __str__(self) -> str:
        return f"{self.nid} bad {self.expr.nid}{self.comment}"


class Btor2Fair(Btor2Node):

    def __init__(self, expr: Btor2Node):
        super().__init__()
        self.expr = expr

    def __str__(self) -> str:
        return f"{self.nid} fair {self.expr.nid}{self.comment}"


class Btor2Program():

    def __init__(self, sorts: set[Btor2Sort], instr: list[Btor2Expr]):
        self.sorts = sorts
        self.instructions = instr

    def __str__(self) -> str:
        s: str  = ""
        for sort in self.sorts:
            s += f"{sort}\n"
        for instruction in self.instructions:
            s += f"{instruction}\n"
        return s[:-1] # delete last newline and return
    

operator_table: dict[Btor2Operator, tuple[list[type], type]] = {
    Btor2Operator.SEXT: ([Btor2BitVec], Btor2BitVec)
}


def postorder_iterative_btor2(expr: Btor2Expr, func: Callable[[Btor2Expr], Any]):
    """Perform an iterative postorder traversal of node, calling func on each node."""
    stack: list[tuple[bool, Btor2Expr]] = []
    visited: set[Btor2Expr] = set()

    stack.append((False, expr))

    while len(stack) > 0:
        (seen, cur) = stack.pop()

        if seen:
            func(cur)
            continue
        elif cur in visited:
            continue

        visited.add(cur)
        stack.append((True, cur))

        for child in [c for c in cur.children if c]:
            stack.append((False, child))