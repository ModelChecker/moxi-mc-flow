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

    def to_json(self) -> dict:
        return {"symbol": self.symbol, "indices": self.indices}


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
        
        if is_bool_sort(self) and is_bool_sort(__value):
            return True
        
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
        if not self.is_parametric():
            return str(self.identifier)

        parameters_str = " ".join([str(p) for p in self.parameters])
        return f"({self.identifier} {parameters_str})"

    def to_json(self) -> dict:
        identifier = self.identifier.to_json()
        parameters = [s.to_json() for s in self.parameters]
        return {"identifier": identifier, "parameters": parameters}


# Built-in sorts
IL_NO_SORT: ILSort = ILSort(ILIdentifier("", []), []) # placeholder sort
IL_BOOL_SORT: ILSort = ILSort(ILIdentifier("Bool", []), [])
IL_INT_SORT: ILSort = ILSort(ILIdentifier("Int", []), [])
IL_BITVEC_SORT: Callable[[int], ILSort] = lambda n: ILSort(ILIdentifier("BitVec", [n]), [])
IL_ARRAY_SORT: Callable[[ILSort, ILSort], ILSort] = lambda A,B: ILSort(ILIdentifier("Array", []), [A,B])
IL_ENUM_SORT:  Callable[[str], ILSort] = lambda s: ILSort(ILIdentifier(s, []), [])


def is_bool_sort(sort: ILSort) -> bool:
    """A Bool sort has an identifier that is the symbol 'Bool' and is non-parametric"""
    return sort.identifier.is_symbol("Bool") and not sort.is_parametric()

def is_bitvec_sort(sort: ILSort) -> bool:
    """A bit vector sort has an identifier with the symbol 'BitVec' and is indexed with a single numeral"""
    return (sort.identifier.symbol == "BitVec" and len(sort.identifier.indices) == 1)

def is_int_sort(sort: ILSort) -> bool:
    """An Int sort has an identifier that is the symbol 'Int' and is non-parametric"""
    return sort.identifier.is_symbol("Int") and not sort.is_parametric()

def is_array_sort(sort: ILSort) -> bool:
    """An Array sort has an identifier that is the symbol 'Array' and has two parameters"""
    return sort.identifier.is_symbol("Array") and not sort.is_parametric() and sort.arity() == 2


class ILExpr():

    def __init__(self, sort: ILSort, children: list[ILExpr]):
        self.sort = sort
        self.children = children

    def __hash__(self) -> int:
        return id(self)

    def to_json(self) -> dict:
        return {}


class ILConstant(ILExpr):

    def __init__(self, sort: ILSort, value: Any):
        super().__init__(sort, [])
        self.value = value

    def __str__(self) -> str:
        if is_bitvec_sort(self.sort):
            format_str = f"#b{'{'}0:0{self.sort.identifier.indices[0]}b{'}'}"
            return format_str.format(self.value)

        return str(self.value)

    def to_json(self) -> dict:
        return {"identifier": str(self)}


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
        return f"{self.symbol}" + "'" if self.prime else ""

    def to_json(self) -> dict:
        return {"identifier": self.symbol + "'" if self.prime else self.symbol}

    def to_json_sorted_var(self) -> dict:
        return {"symbol": self.symbol, "sort": self.sort.to_json()}


IL_EMPTY_VAR = ILVar(ILVarType.NONE, IL_NO_SORT, "", False)


class ILApply(ILExpr):

    def __init__(self, sort: ILSort, identifier: ILIdentifier, children: list[ILExpr]):
        super().__init__(sort, children)
        self.identifier = identifier

    def __str__(self) -> str:
        children_str = " ".join([str(c) for c in self.children])
        return f"({self.identifier} {children_str})"

    def to_json(self) -> dict:
        identifier = self.identifier.to_json()
        args = [c.to_json() for c in self.children]
        return {"identifier": identifier, "args": args}


class ILCommand():

    def to_json(self) -> dict:
        return {}


class ILDeclareSort(ILCommand):

    def __init__(self, symbol: str, arity: int):
        super().__init__()
        self.symbol = symbol
        self.arity = arity

    def __str__(self) -> str:
        return f"(declare-sort {self.symbol} {self.arity})"

    def to_json(self) -> dict:
        return {"command": "declare-sort", "symbol": self.symbol, "arity": self.arity}


class ILDefineSort(ILCommand):

    def __init__(self, symbol: str, parameters: list[str], definition: ILSort):
        super().__init__()
        self.symbol = symbol
        self.parameters = parameters
        self.definition = definition

    def __str__(self) -> str:
        parameters_str = " ".join(self.parameters)
        return f"(define-sort {self.symbol} ({parameters_str}) {self.definition})"

    def to_json(self) -> dict:
        return {
            "command": "define-sort", 
            "symbol": self.symbol, 
            "parameters": self.parameters,
            "definition": self.definition.to_json()    
        }


class ILDeclareEnumSort(ILCommand):

    def __init__(self, symbol: str, values: list[str]):
        super().__init__()
        self.symbol = symbol
        self.values = values

    def __str__(self) -> str:
        values_str = " ".join(self.values)
        return f"(declare-enum-sort {self.symbol} ({values_str}))"

    def to_json(self) -> dict:
        return {
            "command": "declare-enum-sort",
            "symbol": self.symbol,
            "values": self.values
        }


class ILDeclareConst(ILCommand):

    def __init__(self, symbol: str, sort: ILSort):
        super().__init__()
        self.symbol = symbol
        self.sort = sort

    def __str__(self) -> str:
        return f"(declare-const {self.symbol} {self.sort})"

    def to_json(self) -> dict:
        return {
            "command": "declare-const",
            "symbol": self.symbol,
            "values": self.sort.to_json()
        }


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

    def __str__(self) -> str:
        input_str = " ".join([str(i) for i in self.inputs])
        return f"(declare-fun {self.symbol} ({input_str}) {self.output})"

    def to_json(self) -> dict:
        return {
            "command": "declare-fun",
            "symbol": self.symbol,
            "inputs": [i.to_json() for i in self.inputs],
            "output": self.output.to_json()
        }


class ILDefineFun(ILCommand):

    def __init__(
            self, 
            symbol: str, 
            input: list[ILVar], 
            output: ILSort,  
            body: ILExpr):
        super().__init__()
        self.symbol = symbol
        self.input = input
        self.output = output
        self.body = body

    def __str__(self) -> str:
        input_str = " ".join([f"({i.symbol} {i.sort})" for i in self.input])
        return f"(define-fun {self.symbol} ({input_str}) {self.output} {self.body})"

    def to_json(self) -> dict:
        return {
            "command": "define-fun",
            "symbol": self.symbol,
            "inputs": [i.to_json_sorted_var() for i in self.input],
            "output": self.output.to_json(),
            "body": self.body.to_json()
        }


class ILSetLogic(ILCommand):
    
    def __init__(self, logic: str):
        super().__init__()
        self.logic = logic

    def to_json(self) -> dict:
        return {
            "command": "set-logic",
            "symbol": self.logic
        }


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

    def __str__(self) -> str:
        input_str = " ".join([f"({i.symbol} {i.sort})" for i in self.input])
        output_str = " ".join([f"({o.symbol} {o.sort})" for o in self.output])
        local_str = " ".join([f"({l.symbol} {l.sort})" for l in self.input])

        # subsystem_str = ":subsys " # TODO

        s =  f"(define-system {self.symbol} "
        s += f":input ({input_str}) "
        s += f":output ({output_str}) "
        s += f":local ({local_str}) "
        s += f":init {self.init} "
        s += f":trans {self.trans} "
        s += f":inv {self.inv} "
        # s += f":subsys ({input_str}) "

        return s + ")"

    def to_json(self) -> dict:
        return {
            "command": "define-system",
            "symbol": self.symbol,
            "input": [i.to_json_sorted_var() for i in self.input],
            "output": [o.to_json_sorted_var() for o in self.output],
            "local": [l.to_json_sorted_var() for l in self.local],
            "init": self.init.to_json(),
            "trans": self.trans.to_json(),
            "inv": self.inv.to_json(),
            "subsys": [
                {
                    "symbol": s, 
                    "target": {
                        "symbol": t,
                        "arguments": v
                    }
                } for s,(t,v) in self.subsystem_signatures.items()
            ]
        }


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

    def __str__(self) -> str:
        input_str = " ".join([f"({i.symbol} {i.sort})" for i in self.input])
        output_str = " ".join([f"({o.symbol} {o.sort})" for o in self.output])
        local_str = " ".join([f"({l.symbol} {l.sort})" for l in self.input])

        assumption_str = " ".join([f":assumption ({symbol} {expr})" for symbol,expr in self.assumption.items()])
        fairness_str = " ".join([f":fairness ({symbol} {expr})" for symbol,expr in self.fairness.items()])
        reachable_str = " ".join([f":reachable ({symbol} {expr})" for symbol,expr in self.reachable.items()])
        current_str = " ".join([f":current ({symbol} {expr})" for symbol,expr in self.current.items()])

        query_str = " ".join([f"({symbol} ({' '.join(exprs)}))" for symbol,exprs in self.query.items()])

        s =  f"(check-system {self.sys_symbol} "
        s += f":input ({input_str}) "
        s += f":output ({output_str}) "
        s += f":local ({local_str}) "
        s += f"{assumption_str} "
        s += f"{fairness_str} "
        s += f"{reachable_str} "
        s += f"{current_str} "
        s += f":query {query_str} "

        return s + ")"

    def to_json(self) -> dict:
        return {
            "command": "check-system",
            "symbol": self.sys_symbol,
            "input": [i.to_json_sorted_var() for i in self.input],
            "output": [o.to_json_sorted_var() for o in self.output],
            "local": [l.to_json_sorted_var() for l in self.local],
            "assumption": [{"symbol": s, "formula": a.to_json()} for s,a in self.assumption.items()],
            "fairness": [{"symbol": s, "formula": f.to_json()} for s,f in self.fairness.items()],
            "reachable": [{"symbol": s, "formula": r.to_json()} for s,r in self.reachable.items()],
            "current": [{"symbol": s, "formula": c.to_json()} for s,c in self.current.items()],
            "query": [{"symbol": s, "formulas": q} for s,q in self.query.items()],
            "queries": []
        }


class ILProgram():

    def __init__(self, commands: list[ILCommand]):
        self.commands: list[ILCommand] = commands

    def get_check_system_cmds(self) -> list[ILCheckSystem]:
        return [cmd for cmd in self.commands if isinstance(cmd, ILCheckSystem)]

    def __str__(self) -> str:
        return "\n".join(str(cmd) for cmd in self.commands)

    def to_json(self) -> list:
        return [cmd.to_json() for cmd in self.commands]


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
        symbol: str, 
        sort_symbols: set[IdentifierClass],
        function_symbols: set[IdentifierClass],
        sort_check: Callable[[ILApply], bool]
    ):
        self.symbol = symbol
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
        # this works due to assumption of a dependency graph; 
        # there is only one unique order for each system context
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
        # need to implement setters/update functions for each data structure
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
            # TODO: move this warning to il2btor.py
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

            input_sorts = [s.sort for s in cmd.input]
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
                        continue

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

