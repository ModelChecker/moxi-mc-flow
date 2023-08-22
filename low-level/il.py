"""
Representation of IL
"""
from __future__ import annotations
from enum import Enum
import json
import os
import re
from jsonschema import validate, exceptions, RefResolver
from typing import Any, Callable, Optional

# Width of integers -- used when we convert Int sorts to BitVec sorts
INT_WIDTH = 64

class ILAttribute(Enum):
    INPUT      = ":input"
    OUTPUT     = ":output"
    LOCAL      = ":local"
    INIT       = ":init"
    TRANS      = ":trans"
    INV        = ":inv"
    SUBSYS     = ":subsys"
    ASSUMPTION = ":assumption"
    FAIRNESS   = ":fairness"
    REACHABLE  = ":reachable"
    CURRENT    = ":current"
    QUERY      = ":query"

    def is_variable_declaration(self) -> bool:
        return self.value == ":input" or self.value == ":output" or self.value == ":local"

    def is_definable_once(self) -> bool:
        return self.is_variable_declaration() or self.value == ":init"

    def get_value_type(self) -> type:
        if self.value == ":input" or self.value == ":output" or self.value == ":local" or self.value == ":subsys" or self.value == ":assumption" or self.value == ":fairness" or self.value == ":reachable" or self.value == ":current" or self.value == ":query":
            return dict 
        elif self.value == ":init" or self.value == ":trans" or self.value == ":inv":
            return ILExpr

        raise NotImplementedError


class ILIdentifier():
    """
    An identifier is a symbol and can be "indexed" with numerals. As opposed to SMT-LIB2, we restrict indices to numerals and not symbols and numerals.

    See section 3.3 of https://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2021-05-12.pdf.
    """

    def __init__(self, symbol: str, indices: list[int]):
        self.symbol = symbol
        self.indices = indices

    def get_class(self) -> IdentifierClass:
        return (self.symbol, self.num_indices())

    def num_indices(self) -> int:
        return len(self.indices)

    def check(self, __symbol: str, num_indices: int) -> bool:
        return self.symbol == __symbol and len(self.indices) == num_indices

    def is_indexed(self) -> bool:
        return len(self.indices) > 0

    def is_simple(self) -> bool:
        return len(self.indices) == 0

    def is_symbol(self, __symbol: str) -> bool:
        """Returns whether identifier is not indexed and has symbol '__symbol'"""
        return not self.is_indexed() and self.symbol == __symbol

    def __eq__(self, __value: object) -> bool:
        """Two ILIdentifiers are equal if they have the same symbol and indices."""
        if isinstance(__value, str):
            return self.is_symbol(__value)

        if not isinstance(__value, ILIdentifier):
            return False

        if self.symbol != __value.symbol or self.indices != __value.indices:
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
        self.parameters = sorts

    def arity(self) -> int:
        return len(self.parameters)

    def is_parametric(self) -> bool:
        return len(self.parameters) > 0 

    def __eq__(self, __value: object) -> bool:
        if not isinstance(__value, ILSort):
            return False

        if is_bool_sort(self) and is_bitvec_sort(__value) and __value.identifier.indices[0] == 1:
            return True

        if is_bool_sort(__value) and is_bitvec_sort(self) and self.identifier.indices[0] == 1:
            return True

        if self.identifier != __value.identifier:
            return False

        return True
    
    def __hash__(self) -> int:
        # TODO: not effective for parameterized sorts
        if is_bool_sort(self):
            return hash(ILIdentifier("BitVec", [1]))
        return hash(self.identifier)
    
    def __str__(self) -> str:
        s = f"({self.identifier} "
        for sort in self.parameters:
            s += f"{sort} "
        return s[:-1]+")"


# Built-in sorts
IL_NO_SORT: ILSort = ILSort(ILIdentifier("", []), []) # placeholder sort
IL_BOOL_SORT: ILSort = ILSort(ILIdentifier("Bool", []), [])
IL_INT_SORT: ILSort = ILSort(ILIdentifier("Int", []), [])
IL_BITVEC_SORT: Callable[[int], ILSort] = lambda n: ILSort(ILIdentifier("BitVec", [n]), [])
IL_ARRAY_SORT: Callable[[ILSort, ILSort], ILSort] = lambda A,B: ILSort(ILIdentifier("Array", []), [A,B])
IL_ENUM_SORT:  Callable[[str], ILSort] = lambda s: ILSort(ILIdentifier(s, []), [])


def is_bool_sort(sort: ILSort) -> bool:
    """A Bool sort has an identifier that is the symbol 'Bool' and is non-parametric."""
    return sort.identifier.is_symbol("Bool") and not sort.is_parametric()

def is_bitvec_sort(sort: ILSort) -> bool:
    """A bit vector sort has an identifier with the symbol 'BitVec' and is indexed with a single numeral. Bool type is an implicit name for a bit vector of length one."""
    return (sort.identifier.symbol == "BitVec" and len(sort.identifier.indices) == 1) or is_bool_sort(sort)

def is_int_sort(sort: ILSort) -> bool:
    """An Int sort has an identifier that is the symbol 'Int' and is non-parametric."""
    return sort.identifier.is_symbol("Int") and not sort.is_parametric()

def is_array_sort(sort: ILSort) -> bool:
    """An Array sort has an identifier that is the symbol 'Array' and has two parameters"""
    return sort.identifier.is_symbol("Array") and sort.arity() == 2


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


class ILVarType(Enum):
    NONE   = 0
    INPUT  = 1,
    OUTPUT = 2,
    LOCAL  = 3,
    LOGIC  = 4


class ILVar(ILExpr):
    """An ILVar requires a sort and symbol."""

    def __init__(self, var_type: ILVarType, sort: ILSort, symbol: str, prime: bool):
        super().__init__(sort, [])
        self.var_type = var_type
        self.symbol = symbol
        self.prime = prime

    def __eq__(self, __value: object) -> bool:
        """Two ILVars are equal if they have the same symbol."""
        if isinstance(__value, ILVar):
            return self.symbol == __value.symbol
        return False

    def __hash__(self) -> int:
        return hash(self.symbol)

    def __str__(self) -> str:
        return f"{self.symbol}"

    def rename(self, new: str) -> ILVar:
        return ILVar(self.var_type, self.sort, new, self.prime)

IL_EMPTY_VAR = ILVar(ILVarType.NONE, IL_NO_SORT, "", False)


class ILApply(ILExpr):

    def __init__(self, sort: ILSort, identifier: ILIdentifier, children: list[ILExpr]):
        super().__init__(sort, children)
        self.identifier = identifier

    def __str__(self) -> str:
        s = f"({self.identifier} "
        for child in self.children:
            s += f"{child} "
        return s[:-1] + ")"


class ILCommand():
    pass


class ILDeclareSort(ILCommand):

    def __init__(self, symbol: str, arity: int):
        super().__init__()
        self.symbol = symbol
        self.arity = arity


class ILDefineSort(ILCommand):

    def __init__(self, symbol: str, params: list[str], definition: ILSort):
        super().__init__()
        self.symbol = symbol
        self.params = params
        self.definition = definition


class ILDeclareEnumSort(ILCommand):

    def __init__(self, symbol: str, values: list[str]):
        super().__init__()
        self.symbol = symbol
        self.values = values


class ILDeclareConst(ILCommand):

    def __init__(self, symbol: str, sort: ILSort):
        super().__init__()
        self.symbol = symbol
        self.sort = sort


class ILDeclareFun(ILCommand):

    def __init__(
            self, 
            symbol: str, 
            inputs: list[ILSort], 
            output: ILSort):
        super().__init__()
        self.symbol = symbol
        self.inputs = inputs
        self.output = output


class ILDefineFun(ILCommand):

    def __init__(
            self, 
            symbol: str, 
            inputs: list[ILVar], 
            output: ILSort,  
            body: ILExpr):
        super().__init__()
        self.symbol = symbol
        self.inputs = inputs
        self.output = output
        self.body = body


class ILSetLogic(ILCommand):
    
    def __init__(self, logic: str):
        super().__init__()
        self.logic = logic


class ILDefineSystem(ILCommand):
    
    def __init__(
        self, 
        symbol: str,
        input: list[ILVar], 
        output: list[ILVar], 
        local: list[ILVar], 
        init: ILExpr,
        trans: ILExpr, 
        inv: ILExpr,
        subsystems: dict[str, tuple[str, list[str]]]
    ):
        self.symbol = symbol
        self.input = input
        self.local = local
        self.output = output
        self.init = init
        self.trans = trans
        self.inv = inv
        self.subsystem_signatures = subsystems

        # convenient data structures
        self.symbol_map = { var.symbol : var for var in input + output + local }

        # this gets populated by sort checker
        self.subsystems: dict[str, ILDefineSystem] = {}


class ILCheckSystem(ILCommand):
    
    def __init__(
        self, 
        sys_symbol: str,
        input: list[ILVar], 
        output: list[ILVar], 
        local: list[ILVar], 
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


class ILExit(ILCommand):
    pass

# A rank is a function signature. For example:
#   rank(and) = ([Bool, Bool], Bool)
Rank = tuple[list[ILSort], ILSort]

# An identifier class describes a class of identifiers that have the same symbol and number of indices.
# For instance, ("BitVec", 1) describes the class of bit vector sorts and ("extract", 2) describes the 
# class of all bit vector "extract" operators.
IdentifierClass = tuple[str, int]

# RankTable[f,i] = ( par A ( rank(f,A) ) )
#   where rank(f,A) is the rank of function with symbol f and number indices i given parameter(s) A
RankTable = dict[IdentifierClass, Callable[[Any], Rank]]

CORE_RANK_TABLE: RankTable = {
    ("true", 0):     lambda _: ([], IL_BOOL_SORT),
    ("false", 0):    lambda _: ([], IL_BOOL_SORT),
    ("not", 0):      lambda _: ([IL_BOOL_SORT], IL_BOOL_SORT),
    ("=>", 0):       lambda _: ([IL_BOOL_SORT, IL_BOOL_SORT], IL_BOOL_SORT),
    ("and", 0):      lambda _: ([IL_BOOL_SORT, IL_BOOL_SORT], IL_BOOL_SORT),
    ("or", 0):       lambda _: ([IL_BOOL_SORT, IL_BOOL_SORT], IL_BOOL_SORT),
    ("xor", 0):      lambda _: ([IL_BOOL_SORT, IL_BOOL_SORT], IL_BOOL_SORT),
    ("=", 0):        lambda A: ([A,A], IL_BOOL_SORT),
    ("distinct", 0): lambda A: ([A,A], IL_BOOL_SORT),
    ("ite", 0):      lambda A: ([IL_BOOL_SORT, A, A], A),
}

BITVEC_RANK_TABLE: RankTable = {
    ("concat", 0):       lambda A: ([IL_BITVEC_SORT(A[0]), IL_BITVEC_SORT(A[1])], IL_BITVEC_SORT(A[0]+A[1])),
    ("extract", 2):      lambda A: ([IL_BITVEC_SORT(A[0])], IL_BITVEC_SORT(A[1])),
    ("zero_extend", 1):  lambda A: ([IL_BITVEC_SORT(A[0])], IL_BITVEC_SORT(A[0] + A[1])),
    ("sign_extend", 1):  lambda A: ([IL_BITVEC_SORT(A[0])], IL_BITVEC_SORT(A[0] + A[1])),
    ("rotate_left", 1):  lambda A: ([IL_BITVEC_SORT(A)], IL_BITVEC_SORT(A)),
    ("rotate_right", 1): lambda A: ([IL_BITVEC_SORT(A)], IL_BITVEC_SORT(A)),
    ("bvshl", 0):  lambda A: ([IL_BITVEC_SORT(A), IL_BITVEC_SORT(A)], IL_BITVEC_SORT(A)),
    ("bvlshr", 0): lambda A: ([IL_BITVEC_SORT(A), IL_BITVEC_SORT(A)], IL_BITVEC_SORT(A)),
    ("bvashr", 0): lambda A: ([IL_BITVEC_SORT(A), IL_BITVEC_SORT(A)], IL_BITVEC_SORT(A)),
    ("bvnot", 0):  lambda A: ([IL_BITVEC_SORT(A)], IL_BITVEC_SORT(A)),
    ("bvneg", 0):  lambda A: ([IL_BITVEC_SORT(A)], IL_BITVEC_SORT(A)),
    ("bvand", 0):  lambda A: ([IL_BITVEC_SORT(A), IL_BITVEC_SORT(A)], IL_BITVEC_SORT(A)),
    ("bvnand", 0): lambda A: ([IL_BITVEC_SORT(A), IL_BITVEC_SORT(A)], IL_BITVEC_SORT(A)),
    ("bvor", 0):   lambda A: ([IL_BITVEC_SORT(A), IL_BITVEC_SORT(A)], IL_BITVEC_SORT(A)),
    ("bvnor", 0):  lambda A: ([IL_BITVEC_SORT(A), IL_BITVEC_SORT(A)], IL_BITVEC_SORT(A)),
    ("bvxor", 0):  lambda A: ([IL_BITVEC_SORT(A), IL_BITVEC_SORT(A)], IL_BITVEC_SORT(A)),
    ("bvxnor", 0): lambda A: ([IL_BITVEC_SORT(A), IL_BITVEC_SORT(A)], IL_BITVEC_SORT(A)),
    ("bvadd", 0):  lambda A: ([IL_BITVEC_SORT(A), IL_BITVEC_SORT(A)], IL_BITVEC_SORT(A)), 
    ("bvsub", 0):  lambda A: ([IL_BITVEC_SORT(A), IL_BITVEC_SORT(A)], IL_BITVEC_SORT(A)),
    ("bvmul", 0):  lambda A: ([IL_BITVEC_SORT(A), IL_BITVEC_SORT(A)], IL_BITVEC_SORT(A)),
    ("bvudiv", 0): lambda A: ([IL_BITVEC_SORT(A), IL_BITVEC_SORT(A)], IL_BITVEC_SORT(A)),
    ("bvsdiv", 0): lambda A: ([IL_BITVEC_SORT(A), IL_BITVEC_SORT(A)], IL_BITVEC_SORT(A)),
    ("bvurem", 0): lambda A: ([IL_BITVEC_SORT(A), IL_BITVEC_SORT(A)], IL_BITVEC_SORT(A)),
    ("bvsrem", 0): lambda A: ([IL_BITVEC_SORT(A), IL_BITVEC_SORT(A)], IL_BITVEC_SORT(A)),
    ("bvsmod", 0): lambda A: ([IL_BITVEC_SORT(A), IL_BITVEC_SORT(A)], IL_BITVEC_SORT(A)),
    ("bvult", 0):  lambda A: ([IL_BITVEC_SORT(A), IL_BITVEC_SORT(A)], IL_BOOL_SORT),
    ("bvule", 0):  lambda A: ([IL_BITVEC_SORT(A), IL_BITVEC_SORT(A)], IL_BOOL_SORT),
    ("bvugt", 0):  lambda A: ([IL_BITVEC_SORT(A), IL_BITVEC_SORT(A)], IL_BOOL_SORT),
    ("bvuge", 0):  lambda A: ([IL_BITVEC_SORT(A), IL_BITVEC_SORT(A)], IL_BOOL_SORT),
    ("bvslt", 0):  lambda A: ([IL_BITVEC_SORT(A), IL_BITVEC_SORT(A)], IL_BOOL_SORT),
    ("bvsle", 0):  lambda A: ([IL_BITVEC_SORT(A), IL_BITVEC_SORT(A)], IL_BOOL_SORT),
    ("bvsgt", 0):  lambda A: ([IL_BITVEC_SORT(A), IL_BITVEC_SORT(A)], IL_BOOL_SORT),
    ("bvsge", 0):  lambda A: ([IL_BITVEC_SORT(A), IL_BITVEC_SORT(A)], IL_BOOL_SORT),
    ("reduce_and", 0): lambda A: ([IL_BITVEC_SORT(A)], IL_BOOL_SORT),
    ("reduce_or", 0):  lambda A: ([IL_BITVEC_SORT(A)], IL_BOOL_SORT),
    ("reduce_xor", 0): lambda A: ([IL_BITVEC_SORT(A)], IL_BOOL_SORT)
}

ARRAY_RANK_TABLE: RankTable = {
    ("select", 0): lambda A: ([IL_ARRAY_SORT(A[0], A[1]), A[0]], A[1]),
    ("store", 0):  lambda A: ([IL_ARRAY_SORT(A[0], A[1]), A[0], A[1]], IL_ARRAY_SORT(A[0], A[1]))
}


def sort_check_apply_rank(node: ILApply, rank: Rank) -> bool:
    rank_args, rank_return = rank

    if rank_args != [c.sort for c in node.children]:
        return False

    node.sort = rank_return
    return True


def sort_check_apply_core(node: ILApply) -> bool:
    # "true", "false", "not", "=>", "and", "or", "xor", "=", "distinct", "ite"
    identifier = node.identifier
    identifier_class = identifier.get_class()

    if identifier_class not in CORE_RANK_TABLE:
        return False
    elif identifier.check("=", 0) or identifier.check("distinct", 0):
        # (par (A) (= A A Bool))
        # (par (A) (distinct A A Bool))
        if len(node.children) < 1:
            return False

        param = node.children[0].sort
        rank = CORE_RANK_TABLE[(identifier.symbol, 0)](param)

        return sort_check_apply_rank(node, rank)
    elif identifier.check("ite", 0):
        # (par (A) (ite Bool A A A))
        if len(node.children) < 2:
            return False

        param = node.children[1].sort
        rank = CORE_RANK_TABLE[identifier_class](param)

        return sort_check_apply_rank(node, rank)
    # else function is non-parametric

    rank = CORE_RANK_TABLE[identifier_class](None)
    return sort_check_apply_rank(node, rank)


def sort_check_apply_bitvec(node: ILApply) -> bool:
    """Returns true if 'node' corresponds to a valid rank in SMT-LIB2 FixedSizeBitVectors Theory. Assumes that node's identifier is in BITVEC_RANK_TABLE."""
    identifier = node.identifier
    identifier_class = identifier.get_class()

    if identifier_class not in BITVEC_RANK_TABLE:
        return False
    elif identifier.check("concat", 0):
        # (concat (_ BitVec i) (_ BitVec j) (_ BitVec i+j))
        if len(node.children) < 2:
            return False

        operand1 = node.children[0]
        operand2 = node.children[2]
        if not operand1.sort.identifier.is_indexed():
            return False
        elif not operand2.sort.identifier.is_indexed():
            return False

        i = operand1.sort.identifier.indices[0]
        j = operand1.sort.identifier.indices[1]
        rank = BITVEC_RANK_TABLE[identifier_class]((i, j))

        return sort_check_apply_rank(node, rank)
    elif identifier.check("extract", 2):
        # ((_ extract i j) (_ BitVec m) (_ BitVec n))
        # subject to:
        #   - m < i <= j
        #   - n = i - j + 1
        if len(node.children) < 1:
            return False

        operand = node.children[0]
        if not operand.sort.identifier.is_indexed():
            return False

        m = operand.sort.identifier.indices[0]
        (i,j) = identifier.indices

        if j < i or m <= i:
            return False

        n = i - j + 1
        rank = BITVEC_RANK_TABLE[identifier_class]((m, n))

        return sort_check_apply_rank(node, rank)
    elif identifier.check("zero_extend", 1) or identifier.check("sign_extend", 1):
        # ((_ zero_extend i) (_ BitVec m) (_ BitVec m+i))
        # ((_ sign_extend i) (_ BitVec m) (_ BitVec m+i))
        i = identifier.indices[0]

        if len(node.children) < 1:
            return False

        operand = node.children[0]
        if not operand.sort.identifier.is_indexed():
            return False

        m = operand.sort.identifier.indices[0]
        rank = BITVEC_RANK_TABLE[identifier_class]((m, i))

        return sort_check_apply_rank(node, rank)
    elif identifier.check("rotate_left", 1) or identifier.check("rotate_right", 1):
        # ((_ rotate_left i) (_ BitVec m) (_ BitVec m))
        # ((_ rotate_right i) (_ BitVec m) (_ BitVec m))
        if len(node.children) < 1:
            return False

        operand = node.children[0]
        if not operand.sort.identifier.is_indexed():
            return False

        m = operand.sort.identifier.indices[0]
        rank = BITVEC_RANK_TABLE[identifier_class](m)

        return sort_check_apply_rank(node, rank)

    if len(node.children) < 1:
        return False

    operand = node.children[0]
    if not operand.sort.identifier.is_indexed():
        return False

    m = operand.sort.identifier.indices[0]
    rank = BITVEC_RANK_TABLE[identifier_class](m)

    return sort_check_apply_rank(node, rank)


def sort_check_apply_arrays(node: ILApply) -> bool:
    """Returns true if 'node' corresponds to a valid function signature in SMT-LIB2 ArraysEx Theory. Assume that node's identifier is in ARRAY_RANK_TABLE."""
    identifier = node.identifier
    identifier_class = identifier.get_class()

    if identifier_class not in ARRAY_RANK_TABLE:
        return False

    # (par (X Y) (select (Array X Y) X Y)
    # (par (X Y) (store (Array X Y) X Y (Array X Y)))
    if len(node.children) < 1:
        return False

    operand_1 = node.children[0]

    if not is_array_sort(operand_1.sort):
        return False

    X = operand_1.sort.parameters[0]
    Y = operand_1.sort.parameters[1]
    rank = ARRAY_RANK_TABLE[identifier_class]((X, Y))

    return sort_check_apply_rank(node, rank)


def sort_check_apply_qf_bv(node: ILApply) -> bool:
    identifier_class = (node.identifier.symbol, node.identifier.num_indices())

    if identifier_class in CORE_RANK_TABLE:
        return sort_check_apply_core(node)
    elif identifier_class in BITVEC_RANK_TABLE:
        return sort_check_apply_bitvec(node)

    return False


def sort_check_apply_qf_abv(node: ILApply) -> bool:
    identifier_class = (node.identifier.symbol, node.identifier.num_indices())

    if identifier_class in CORE_RANK_TABLE:
        return sort_check_apply_core(node)
    elif identifier_class in BITVEC_RANK_TABLE:
        return sort_check_apply_bitvec(node)
    elif identifier_class in ARRAY_RANK_TABLE:
        return sort_check_apply_arrays(node)
    
    return False


class ILLogic():
    """An ILLogic has a name, a set of sort symbols, a set of function symbols, and a sort_check function"""

    def __init__(
        self, 
        name: str, 
        sort_symbols: set[IdentifierClass],
        function_symbols: set[IdentifierClass],
        sort_check: Callable[[ILApply], bool]
    ):
        self.name = name
        self.sort_symbols = sort_symbols
        self.function_symbols = function_symbols
        self.sort_check = sort_check

        self.symbols = sort_symbols | function_symbols


QF_BV = ILLogic("QF_BV", 
                {("BitVec", 1)}, 
                CORE_RANK_TABLE.keys() | BITVEC_RANK_TABLE.keys(), 
                sort_check_apply_qf_bv)

QF_ABV = ILLogic("QF_ABV", 
                {("BitVec", 1), ("Array", 0)}, 
                CORE_RANK_TABLE.keys() | BITVEC_RANK_TABLE.keys() | ARRAY_RANK_TABLE.keys(), 
                sort_check_apply_qf_abv)


class ILSystemContext():

    def __init__(self):
        self._system_stack: list[tuple[str, ILDefineSystem]] = []

    def push(self, sys: tuple[str, ILDefineSystem]):
        self._system_stack.append(sys)

    def pop(self) -> tuple[str, ILDefineSystem]:
        return self._system_stack.pop()

    def copy(self) -> ILSystemContext:
        new_system_stack = self._system_stack.copy()
        new = ILSystemContext()
        for s in new_system_stack:
            new.push(s)
        return new

    def get_top_level(self) -> Optional[tuple[str, ILDefineSystem]]:
        if len(self._system_stack) == 0:
            return None
        return self._system_stack[0]

    def get_subsystems(self) -> list[tuple[str, ILDefineSystem]]:
        if len(self._system_stack) < 2:
            return []
        return self._system_stack[1:]

    def get_scope_symbols(self) -> list[str]:
        top_level = self.get_top_level()
        if not top_level:
            return []
        top_level_symbol, top_level_system = top_level
        return [top_level_symbol] + [name for name,sys in self.get_subsystems()]

    def __eq__(self, __o: object) -> bool:
        if not isinstance(__o, ILSystemContext):
            return False
        
        if len(__o._system_stack) != len(self._system_stack):
            return False
        
        for (s1, s2) in zip(__o._system_stack, self._system_stack):
            if s1 != s2:
                return False

        return True
        
    def __hash__(self) -> int:
        # TODO: need hash that is sensitive to order?
        # I think this may work due to the assumption of a dependency graph
        # i.e., there is only one unique order for each system context
        return sum([hash(name)+hash(sys.symbol) for name,sys in self._system_stack])


class ILContext():

    def __init__(self):
        self.declared_sorts: dict[ILIdentifier, int] = {}
        self.declared_enum_sorts: dict[str, list[str]] = {}
        self.defined_sorts: set[ILSort] = set()
        self.declared_functions: dict[str, Rank] = {}
        self.defined_functions: dict[str, tuple[Rank, ILExpr]] = {}
        self.defined_systems: dict[str, ILDefineSystem] = {}
        self.logic = QF_ABV # for now, assume QF_BV logic
        self.input_var_sorts: dict[ILVar, ILSort] = {}
        self.output_var_sorts: dict[ILVar, ILSort] = {}
        self.local_var_sorts: dict[ILVar, ILSort] = {}
        self.system_context = ILSystemContext() # used during system flattening

    def get_symbols(self) -> set[str]:
        # TODO: this is computed EVERY time, optimize this
        symbols = set()

        symbols.update([id.symbol for id in self.declared_sorts])
        symbols.update([id for id in self.declared_enum_sorts])
        for syms in self.declared_enum_sorts.values():
            symbols.update(syms)
        symbols.update([srt.identifier.symbol for srt in self.defined_sorts])
        symbols.update([sym for sym in self.declared_functions])
        symbols.update([sym for sym in self.defined_functions])
        symbols.update([sym for sym in self.defined_systems])

        return symbols

    def get_enum_symbols(self) -> set[str]:
        symbols: set[str] = set()
        for syms in self.declared_enum_sorts.values():
            symbols.update(syms)
        return symbols


class ILProgram():

    def __init__(self, commands: list[ILCommand]):
        self.commands: list[ILCommand] = commands

    def get_check_system_cmds(self) -> list[ILCheckSystem]:
        return [cmd for cmd in self.commands if isinstance(cmd, ILCheckSystem)]


def postorder_iterative(expr: ILExpr, func: Callable[[ILExpr], Any]):
    """Perform an iterative postorder traversal of 'expr', calling 'func' on each node."""
    stack: list[tuple[bool, ILExpr]] = []
    visited: set[int] = set()

    stack.append((False, expr))

    while len(stack) > 0:
        (seen, cur) = stack.pop()

        if seen:
            func(cur)
            continue
        elif id(cur) in visited:
            continue

        visited.add(id(cur))
        stack.append((True, cur))
        for child in cur.children:
            stack.append((False, child))


def sort_check(program: ILProgram) -> tuple[bool, ILContext]:
    context: ILContext = ILContext()
    status: bool = True

    def sort_check_expr(node: ILExpr, no_prime: bool, prime_input: bool) -> bool:
        """Return true if node is well-sorted where 'no_prime' is true if primed variables are disabled and 'prime_input' is true if input variable are allowed to be primed (true for check-system assumptions and reachability conditions). """
        nonlocal context

        if isinstance(node, ILConstant):
            return True
        elif isinstance(node, ILVar) and node in context.input_var_sorts:
            node.var_type = ILVarType.INPUT
            node.sort = context.input_var_sorts[node]

            if node.prime and not prime_input:
                print(f"Error: primed input variables only allowed in check system assumptions and reachability conditions ({node.symbol}).")
                return False

            return True
        elif isinstance(node, ILVar) and node in context.output_var_sorts:
            node.var_type = ILVarType.OUTPUT
            node.sort = context.output_var_sorts[node]

            if node.prime and no_prime:
                print(f"Error: primed variables only allowed in system transition relation ({node.symbol}).")
                return False

            return True
        elif isinstance(node, ILVar) and node in context.local_var_sorts:
            node.var_type = ILVarType.LOCAL
            node.sort = context.local_var_sorts[node]

            if node.prime and no_prime:
                print(f"Error: primed variables only allowed in system transition relation ({node.symbol}).")
                return False

            return True
        elif isinstance(node, ILVar):
            print(f"Error: symbol `{node.symbol}` not declared.")
            return False
        elif isinstance(node, ILApply):
            if node.identifier.get_class() in context.logic.function_symbols:
                for arg in node.children:
                    sort_check_expr(arg, no_prime, prime_input)

                if not context.logic.sort_check(node):
                    print(f"Error: function signature does not match definition ({node}).")
                    return False
            elif node.identifier.symbol in context.defined_functions:
                (rank, expr) = context.defined_functions[node.identifier.symbol]

                if not sort_check_apply_rank(node, rank):
                    print(f"Error: function call does not match definition ({node}).")
                    return False
            else:
                print(f"Error: symbol '{node.identifier.symbol}' not recognized ({node}).")
                return False

            return True
        else:
            print(f"Error: node type '{node.__class__}' not recognized ({node}).")
            return False
    # end sort_check_expr

    for cmd in program.commands:
        if isinstance(cmd, ILDeclareSort):
            print(f"Warning: declare-sort command unsupported, ignoring.")
        elif isinstance(cmd, ILDefineSort):
            if cmd.symbol in context.get_symbols():
                print(f"Error: symbol '{cmd.symbol}' already in use.")
                status = False

            # TODO
        elif isinstance(cmd, ILDeclareEnumSort):
            if cmd.symbol in context.get_symbols():
                print(f"Error: symbol '{cmd.symbol}' already in use.")
                status = False

            context.declared_enum_sorts[cmd.symbol] = cmd.values
        elif isinstance(cmd, ILDeclareConst):
            if cmd.symbol in context.get_symbols():
                print(f"Error: symbol '{cmd.symbol}' already in use.")
                status = False

            context.declared_functions[cmd.symbol] = Rank(([], cmd.sort))
        elif isinstance(cmd, ILDeclareFun):
            if cmd.symbol in context.get_symbols():
                print(f"Error: symbol '{cmd.symbol}' already in use.")
                status = False

            context.declared_functions[cmd.symbol] = Rank((cmd.inputs, cmd.output))
        elif isinstance(cmd, ILDefineFun):
            if cmd.symbol in context.get_symbols():
                print(f"Error: symbol '{cmd.symbol}' already in use.")
                status = False

            input_sorts = [s.sort for s in cmd.inputs]
            context.defined_functions[cmd.symbol] = (Rank((input_sorts, cmd.output)), cmd.body)
        elif isinstance(cmd, ILDefineSystem):
            # TODO: check for variable name clashes across cmd.input, cmd.output, cmd.local
            context.input_var_sorts = {var:var.sort for var in cmd.input}
            context.output_var_sorts = {var:var.sort for var in cmd.output}
            context.local_var_sorts = {var:var.sort for var in cmd.local}

            status = status and sort_check_expr(cmd.init, True, False)
            status = status and sort_check_expr(cmd.trans, False, False)
            status = status and sort_check_expr(cmd.inv, True, False)

            for name,subsystem in cmd.subsystem_signatures.items():
                # TODO: check for cycles in system dependency graph
                (sys_symbol, signature_symbols) = subsystem

                if sys_symbol not in context.defined_systems:
                    print(f"Error: system '{sys_symbol}' not defined in context.")
                    status = False

                # check that each symbol in signature is in the context
                signature: list[ILVar] = []
                variables: dict[str, ILVar] = {var.symbol:var for var in cmd.input + cmd.output + cmd.local}
                for symbol in signature_symbols:
                    if symbol not in variables:
                        print(f"Error: variable '{symbol}' not declared.")
                        status = False
                        signature.append(IL_EMPTY_VAR)
                    else:
                        signature.append(variables[symbol])
                        if variables[symbol] in cmd.input:
                            variables[symbol].var_type = ILVarType.INPUT
                        elif variables[symbol] in cmd.output:
                            variables[symbol].var_type = ILVarType.OUTPUT
                        elif variables[symbol] in cmd.local:
                            variables[symbol].var_type = ILVarType.LOCAL

                target_system = context.defined_systems[sys_symbol]
                target_signature = target_system.input + target_system.output

                if len(signature) != len(target_signature):
                    print(f"Error: subsystem signature does not match target system ({sys_symbol}).\n\t{context.defined_systems[sys_symbol].input + context.defined_systems[sys_symbol].output}\n\t{signature}")
                    status = False
                    continue

                for cmd_var,target_var in zip(signature, target_signature):
                    if cmd_var.sort != target_var.sort:
                        print(f"Error: subsystem signature does not match target system ({sys_symbol}).\n\t{context.defined_systems[sys_symbol].input + context.defined_systems[sys_symbol].output}\n\t{signature}")
                        status = False
                        continue

                cmd.subsystems[name] = context.defined_systems[sys_symbol]

            context.defined_systems[cmd.symbol] = cmd

            context.input_var_sorts = {}
            context.output_var_sorts = {}
            context.local_var_sorts = {}
        elif isinstance(cmd, ILCheckSystem):
            if not cmd.sys_symbol in context.defined_systems:
                print(f"Error: system '{cmd.sys_symbol}' undefined.")
                status = False
                continue

            context.input_var_sorts = {var:var.sort for var in cmd.input}
            context.output_var_sorts = {var:var.sort for var in cmd.output}
            context.local_var_sorts = {var:var.sort for var in cmd.local}

            system = context.defined_systems[cmd.sys_symbol]

            if len(system.input) != len(cmd.input):
                print(f"Error: input variables do not match target system ({system.symbol}).\n\t{system.input}\n\t{cmd.input}")
                status = False
                continue

            for i1,i2 in zip(system.input, cmd.input):
                if i1.sort != i2.sort:
                    print(f"Error: sorts do not match in check-system (expected {i1.sort}, got {i2.sort})")
                    status = False
                else:
                    i2.var_type = ILVarType.INPUT
                # cmd.rename_map[v1] = v2

            if len(system.output) != len(cmd.output):
                print(f"Error: output variables do not match target system ({system.symbol}).\n\t{system.output}\n\t{cmd.output}")
                status = False
                continue

            for o1,o2 in zip(system.output, cmd.output):
                if o1.sort != o2.sort:
                    print(f"Error: sorts do not match in check-system (expected {o1.sort}, got {o2.sort})")
                    status = False
                else:
                    o2.var_type = ILVarType.OUTPUT
                # cmd.rename_map[v1] = v2

            if len(system.local) != len(cmd.local):
                print(f"Error: local variables do not match target system ({system.symbol}).\n\t{system.input}\n\t{cmd.input}")
                status = False
                continue

            for l1,l2 in zip(system.local, cmd.local):
                if l1.sort != l2.sort:
                    print(f"Error: sorts do not match in check-system (expected {l1.sort}, got {l2.sort})")
                    status = False
                else:
                    l2.var_type = ILVarType.LOCAL
                # cmd.rename_map[v1] = v2

            for expr in cmd.assumption.values():
                status = status and sort_check_expr(expr, False, True)

            for expr in cmd.reachable.values():
                status = status and sort_check_expr(expr, False, True)

            for expr in cmd.fairness.values():
                status = status and sort_check_expr(expr, False, True)

            for expr in cmd.current.values():
                status = status and sort_check_expr(expr, False, True)

            context.input_var_sorts = {}
            context.output_var_sorts = {}
            context.local_var_sorts = {}
        else:
            raise NotImplementedError

    return (status, context)


def from_json_identifier(contents: dict | str) -> ILIdentifier:
    if isinstance(contents, dict):
        return ILIdentifier(contents["symbol"], contents["indices"])
    else: # isinstance(contents, str)
        return ILIdentifier(contents, [])


def from_json_sort(contents: dict) -> ILSort:
    params: list[ILSort] =  []
    if "parameters" in contents:
        params = [from_json_sort(param) for param in contents["parameters"]]

    identifier = from_json_identifier(contents["identifier"])

    return ILSort(identifier, params)


def from_json_sorted_var(contents: dict) -> ILVar:
    sort = from_json_sort(contents["sort"])
    return ILVar(ILVarType.NONE, sort, contents["symbol"], False)


def from_json_expr(contents: dict, enums: dict[str, str]) ->  ILExpr:
    args: list[ILExpr] = []
    if "args" in contents:
        args = [from_json_expr(a, enums) for a in contents["args"]]
    
    identifier = from_json_identifier(contents["identifier"])

    if len(args) != 0:
        return ILApply(IL_NO_SORT, identifier, args)
    
    if re.match(r"0|[1-9]\d*", identifier.symbol):
        return ILConstant(IL_INT_SORT, int(identifier.symbol))
    elif re.match(r"#x[A-F0-9]+", identifier.symbol):
        return ILConstant(IL_BITVEC_SORT(len(identifier.symbol[2:])*4), int(identifier.symbol[2:], base=16))
    elif re.match(r"#b[01]+", identifier.symbol):
        return ILConstant(IL_BITVEC_SORT(len(identifier.symbol[2:])), int(identifier.symbol[2:], base=2))
    elif identifier.symbol in enums:
        return ILConstant(IL_ENUM_SORT(enums[identifier.symbol]), identifier.symbol)
    # else is variable

    prime: bool = False
    symbol: str = identifier.symbol
    if symbol[len(symbol)-1] == "'":
        prime = True
        symbol = symbol[:-1]

    return ILVar(ILVarType.NONE, IL_NO_SORT, symbol, prime)


def from_json(contents: dict) -> Optional[ILProgram]:
    dirname = os.path.dirname(__file__)

    with open(f"{dirname}/IL-JSON/schema/il.json", "r") as f:
        il_schema = json.load(f)

    resolver = RefResolver(f"file://{dirname}/IL-JSON/schema/", {})

    try:
        validate(contents, il_schema, resolver=resolver)
    except exceptions.SchemaError as se:
        print("Error: json schema invalid", se)
        return None
    except exceptions.ValidationError as ve:
        print("Error: json failed validation against schema.", ve)
        return None
    
    program: list[ILCommand] = []
    enums: dict[str, str] = {} # maps enum values to their sort symbol

    for cmd in contents:
        if cmd["command"] == "declare-sort":
            new = ILDeclareSort(cmd["symbol"], int(cmd["arity"]))
            program.append(new)
        elif cmd["command"] == "define-sort":
            definition = from_json_sort(cmd["definition"])
            new = ILDefineSort(cmd["symbol"], cmd["parameters"], definition)
            program.append(new)
        elif cmd["command"] == "declare-enum-sort":
            values = []
            for value in cmd["values"]:
                values.append(value)
                enums[value] = cmd["symbol"]

            new = ILDeclareEnumSort(cmd["symbol"], values)
            program.append(new)
        elif cmd["command"] == "declare-const":
            sort = from_json_sort(cmd["sort"])

            new = ILDeclareConst(cmd["symbol"], sort)
            program.append(new)
        elif cmd["command"] == "declare-fun":
            pass
        elif cmd["command"] == "define-fun":
            inputs = [from_json_sorted_var(i) for i in cmd["inputs"]]
            output = from_json_sort(cmd["output"])
            body = from_json_expr(cmd["body"], enums)

            new = ILDefineFun(cmd["symbol"], inputs, output, body)
            program.append(new)
        elif cmd["command"] == "define-system":
            input, output, local = [], [], []
            init, trans, inv = ILConstant(IL_BOOL_SORT, True), ILConstant(IL_BOOL_SORT, True), ILConstant(IL_BOOL_SORT, True)
            subsys = {}

            if "input" in cmd:
                input =  [from_json_sorted_var(i) for i in cmd["input"]]
            if "output" in cmd:
                output =  [from_json_sorted_var(i) for i in cmd["output"]]
            if "local" in cmd:
                local =  [from_json_sorted_var(i) for i in cmd["local"]]

            if "init" in cmd:
                init = from_json_expr(cmd["init"], enums)
            if "trans" in cmd:
                trans = from_json_expr(cmd["trans"], enums)
            if "inv" in cmd:
                inv = from_json_expr(cmd["inv"], enums)

            if "subsys" in cmd:
                for subsystem in cmd["subsys"]:
                    target = subsystem["target"]
                    subsys[subsystem["symbol"]] = (target["symbol"], target["arguments"])
                
            new  = ILDefineSystem(cmd["symbol"],  input, output, local, init, trans, inv, subsys)
            program.append(new)
        elif cmd["command"] == "check-system":
            # TODO: queries
            input, output, local = [], [], []
            assumption, reachable, fairness, current, query, queries = {}, {}, {}, {}, {}, {}

            if "input" in cmd:
                input =  [from_json_sorted_var(i) for i in cmd["input"]]
            if "output" in cmd:
                output =  [from_json_sorted_var(i) for i in cmd["output"]]
            if "local" in cmd:
                local =  [from_json_sorted_var(i) for i in cmd["local"]]

            if "assumption" in cmd:
                assumption = { entry["symbol"]: from_json_expr(entry["formula"], enums) for entry in cmd["assumption"] }
            if "reachable" in cmd:
                reachable = { entry["symbol"]: from_json_expr(entry["formula"], enums) for entry in cmd["reachable"] }
            if "fairness" in cmd:
                fairness = { entry["symbol"]: from_json_expr(entry["formula"], enums) for entry in cmd["fairness"] }
            if "current" in cmd:
                current = { entry["symbol"]: from_json_expr(entry["formula"], enums) for entry in cmd["current"] }

            if "query" in cmd:
                query = { entry["symbol"]: entry["formulas"] for entry in cmd["query"] }
                
            new  = ILCheckSystem(cmd["symbol"],  input, output, local, assumption, fairness, reachable, current, query)
            program.append(new)

    return ILProgram(program)