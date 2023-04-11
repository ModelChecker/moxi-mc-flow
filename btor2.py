"""
https://fmv.jku.at/papers/NiemetzPreinerWolfBiere-CAV18.pdf
"""
from enum import Enum


class Btor2Operator(Enum):
    # indexed
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
        return self.value >= 100 and self.value < 200

    def is_binary(self) -> bool:
        return self.value >= 200 and self.value < 300

    def is_ternary(self) -> bool:
        return self.value >= 300 and self.value < 400


class Btor2Node():

    def __init__(self) -> None:
        self.nid = -1


class Btor2Sort(Btor2Node):

    def __init__(self) -> None:
        super().__init__()
        self.sid = -1


class Btor2BitVec(Btor2Sort):

    def __init__(self, len: int) -> None:
        super().__init__()
        self.length = len
        self.name = "bitvec"
        
    def __str__(self) -> str:
        return f"{self.nid} {self.name} {self.length}"
    
    def __eq__(self, __value: object) -> bool:
        if isinstance(__value, Btor2BitVec):
            return self.length == __value.length
        else:
            return False


class Btor2Array(Btor2Sort):

    def __init__(self, domain: Btor2Sort, range: Btor2Sort) -> None:
        super().__init__()
        self.domain = domain
        self.range = range
        self.name = "array"

    def __str__(self) -> str:
        return f"{self.nid} {self.name} {self.domain.sid} {self.range.sid}"
    
    def __eq__(self, __value: object) -> bool:
        if isinstance(__value, Btor2Array):
            return self.domain == __value.domain and self.range == __value.range
        else:
            return False


class Btor2Expr(Btor2Node):

    def __init__(self) -> None:
        super().__init__()


class Btor2Var(Btor2Expr):

    def __init__(self) -> None:
        super().__init__()


class Btor2InputVar(Btor2Var):

    def __init__(self, sort) -> None:
        super().__init__()
        self.sort: Btor2Sort = sort

    def __str__(self) -> str:
        return f"{self.nid} input {self.sort.sid}"


class Btor2StateVar(Btor2Var):

    def __init__(self, sort) -> None:
        super().__init__()
        self.sort: Btor2Sort = sort

    def __str__(self) -> str:
        return f"{self.nid} state {self.sort.sid}"


class Btor2Const(Btor2Expr):

    def __init__(self, sort: Btor2Sort, val: Btor2Node) -> None:
        super().__init__()
        self.sort = sort
        self.value = val


class Btor2Apply(Btor2Expr):

    def __init__(self, sort: Btor2Sort, op: Btor2Operator, args: list[Btor2Expr]) -> None:
        super().__init__()
        self.sort = sort
        self.operator = op


class Btor2Program():

    def __init__(self, sorts: set[Btor2Sort], instr: list[Btor2Expr]) -> None:
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