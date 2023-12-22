"""
Representation of IL
"""
from __future__ import annotations

from enum import Enum
from typing import Any, Callable, Optional

from .util import eprint # type: ignore

# Width of integers -- used when we convert Int sorts to BitVec sorts
INT_WIDTH = 64

class MCILAttribute(Enum):
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
            return dict # type: ignore
        elif self.value == ":init" or self.value == ":trans" or self.value == ":inv":
            return MCILExpr

        raise NotImplementedError


class MCILIdentifier():
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

        if not isinstance(__value, MCILIdentifier):
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

    
    def to_json(self) -> dict: # type: ignore
        return {"symbol": self.symbol, "indices": self.indices} # type: ignore


class MCILSort():

    def __init__(self, identifier: MCILIdentifier, sorts: list[MCILSort]):
        self.identifier = identifier
        self.parameters = sorts

    def arity(self) -> int:
        return len(self.parameters)

    def is_parametric(self) -> bool:
        return len(self.parameters) > 0 

    def __eq__(self, __value: object) -> bool:
        if not isinstance(__value, MCILSort):
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
            return hash(MCILIdentifier("BitVec", [1]))
        elif is_array_sort(self):
            return hash((self.identifier, self.parameters[0], self.parameters[1]))
        return hash(self.identifier)
    
    def __str__(self) -> str:
        if not self.is_parametric():
            return str(self.identifier)

        parameters_str = " ".join([str(p) for p in self.parameters])
        return f"({self.identifier} {parameters_str})"

    def to_json(self) -> dict: # type: ignore
        identifier = self.identifier.to_json() # type: ignore
        parameters = [s.to_json() for s in self.parameters] # type: ignore
        return {"identifier": identifier, "parameters": parameters} # type: ignore


# Built-in sorts
MCIL_NO_SORT: MCILSort = MCILSort(MCILIdentifier("", []), []) # placeholder sort
MCIL_BOOL_SORT: MCILSort = MCILSort(MCILIdentifier("Bool", []), [])
MCIL_INT_SORT: MCILSort = MCILSort(MCILIdentifier("Int", []), [])
MCIL_BITVEC_SORT: Callable[[int], MCILSort] = lambda n: MCILSort(MCILIdentifier("BitVec", [n]), [])
MCIL_ARRAY_SORT: Callable[[MCILSort, MCILSort], MCILSort] = lambda A,B: MCILSort(MCILIdentifier("Array", []), [A,B])
MCIL_ENUM_SORT:  Callable[[str], MCILSort] = lambda s: MCILSort(MCILIdentifier(s, []), [])


def is_bool_sort(sort: MCILSort) -> bool:
    """A Bool sort has an identifier that is the symbol 'Bool' and is non-parametric"""
    return sort.identifier.is_symbol("Bool") and not sort.is_parametric()

def is_bitvec_sort(sort: MCILSort) -> bool:
    """A bit vector sort has an identifier with the symbol 'BitVec' and is indexed with a single numeral"""
    return (sort.identifier.symbol == "BitVec" and len(sort.identifier.indices) == 1)

def is_int_sort(sort: MCILSort) -> bool:
    """An Int sort has an identifier that is the symbol 'Int' and is non-parametric"""
    return sort.identifier.is_symbol("Int") and not sort.is_parametric()

def is_array_sort(sort: MCILSort) -> bool:
    """An Array sort has an identifier that is the symbol 'Array' and has two parameters"""
    return sort.identifier.is_symbol("Array") and sort.arity() == 2
    

class MCILExpr():

    def __init__(self, sort: MCILSort, children: list[MCILExpr]):
        self.sort = sort
        self.children = children

    def __hash__(self) -> int:
        return id(self)

    def to_json(self) -> dict: # type: ignore
        return {} # type: ignore


class MCILConstant(MCILExpr):

    def __init__(self, sort: MCILSort, value: Any):
        super().__init__(sort, [])
        self.value = value

    def __str__(self) -> str:
        if is_bool_sort(self.sort):
            return str(self.value).lower()
            
        if is_bitvec_sort(self.sort):
            format_str = f"#b{'{'}0:0{self.sort.identifier.indices[0]}b{'}'}"
            return format_str.format(self.value)

        return str(self.value)

    def to_json(self) -> dict: # type: ignore
        return {"identifier": str(self)} # type: ignore


class MCILVarType(Enum):
    NONE   = 0
    INPUT  = 1,
    OUTPUT = 2,
    LOCAL  = 3,
    LOGIC  = 4


class MCILVar(MCILExpr):
    """An ILVar requires a sort and symbol."""

    def __init__(self, var_type: MCILVarType, sort: MCILSort, symbol: str, prime: bool):
        super().__init__(sort, [])
        self.var_type = var_type
        self.symbol = symbol
        self.prime = prime

    def __eq__(self, __value: object) -> bool:
        """Two ILVars are equal if they have the same symbol."""
        if isinstance(__value, MCILVar):
            return self.symbol == __value.symbol
        return False

    def __hash__(self) -> int:
        return hash(self.symbol)

    def __str__(self) -> str:
        return f"{self.symbol}" + ("'" if self.prime else "")

    def to_json(self) -> dict: # type: ignore
        return {"identifier": self.symbol + ("'" if self.prime else "")} # type: ignore

    def to_json_sorted_var(self) -> dict: # type: ignore
        return {"symbol": self.symbol, "sort": self.sort.to_json()} # type: ignore


MCIL_EMPTY_VAR = MCILVar(MCILVarType.NONE, MCIL_NO_SORT, "", False)


class MCILApply(MCILExpr):

    def __init__(self, sort: MCILSort, identifier: MCILIdentifier, children: list[MCILExpr]):
        super().__init__(sort, children)
        self.identifier = identifier

    def __str__(self) -> str:
        children_str = " ".join([str(c) for c in self.children])
        return f"({self.identifier} {children_str})"

    def to_json(self) -> dict: # type: ignore
        identifier = self.identifier.to_json() # type: ignore
        args = [c.to_json() for c in self.children] # type: ignore
        return {"identifier": identifier, "args": args} # type: ignore


class MCILCommand():

    def get_exprs(self) -> list[MCILExpr]:
        return []

    def to_json(self) -> dict: # type: ignore
        return {} # type: ignore


class MCILDeclareSort(MCILCommand):

    def __init__(self, symbol: str, arity: int):
        super().__init__()
        self.symbol = symbol
        self.arity = arity

    def __str__(self) -> str:
        return f"(declare-sort {self.symbol} {self.arity})"

    def to_json(self) -> dict: # type: ignore
        return {"command": "declare-sort", "symbol": self.symbol, "arity": self.arity} # type: ignore


class MCILDefineSort(MCILCommand):

    def __init__(self, symbol: str, parameters: list[str], definition: MCILSort):
        super().__init__()
        self.symbol = symbol
        self.parameters = parameters
        self.definition = definition

    def __str__(self) -> str:
        parameters_str = " ".join(self.parameters)
        return f"(define-sort {self.symbol} ({parameters_str}) {self.definition})"

    def to_json(self) -> dict: # type: ignore
        return {
            "command": "define-sort",  # type: ignore
            "symbol": self.symbol,  # type: ignore
            "parameters": self.parameters, # type: ignore
            "definition": self.definition.to_json() # type: ignore
        }


class MCILDeclareEnumSort(MCILCommand):

    def __init__(self, symbol: str, values: list[str]):
        super().__init__()
        self.symbol = symbol
        self.values = values

    def __str__(self) -> str:
        values_str = " ".join(self.values)
        return f"(declare-enum-sort {self.symbol} ({values_str}))"

    def to_json(self) -> dict: # type: ignore
        return {
            "command": "declare-enum-sort", # type: ignore
            "symbol": self.symbol, # type: ignore
            "values": self.values # type: ignore
        }


class MCILDeclareConst(MCILCommand):

    def __init__(self, symbol: str, sort: MCILSort):
        super().__init__()
        self.symbol = symbol
        self.sort = sort

    def __str__(self) -> str:
        return f"(declare-const {self.symbol} {self.sort})"

    def to_json(self) -> dict: # type: ignore
        return {
            "command": "declare-const", # type: ignore
            "symbol": self.symbol, # type: ignore
            "values": self.sort.to_json() # type: ignore
        }


class MCILDeclareFun(MCILCommand):

    def __init__(
            self, 
            symbol: str, 
            inputs: list[MCILSort], 
            output: MCILSort):
        super().__init__()
        self.symbol = symbol
        self.inputs = inputs
        self.output_sort = output

    def __str__(self) -> str:
        input_str = " ".join([str(i) for i in self.inputs])
        return f"(declare-fun {self.symbol} ({input_str}) {self.output_sort})"

    def to_json(self) -> dict: # type: ignore
        return {
            "command": "declare-fun", # type: ignore
            "symbol": self.symbol, # type: ignore
            "inputs": [i.to_json() for i in self.inputs], # type: ignore
            "output": self.output_sort.to_json() # type: ignore
        }


class MCILDefineFun(MCILCommand):

    def __init__(
            self, 
            symbol: str, 
            input: list[MCILVar], 
            output: MCILSort,  
            body: MCILExpr):
        super().__init__()
        self.symbol = symbol
        self.inputs = input
        self.output_sort = output
        self.body = body

    def get_exprs(self) -> list[MCILExpr]:
        return [self.body]

    def __str__(self) -> str:
        input_str = " ".join([f"({i.symbol} {i.sort})" for i in self.inputs])
        return f"(define-fun {self.symbol} ({input_str}) {self.output_sort} {self.body})"

    def to_json(self) -> dict: # type: ignore
        return {
            "command": "define-fun", # type: ignore
            "symbol": self.symbol, # type: ignore
            "inputs": [i.to_json_sorted_var() for i in self.inputs], # type: ignore
            "output": self.output_sort.to_json(), # type: ignore
            "body": self.body.to_json() # type: ignore
        }


class MCILSetLogic(MCILCommand):
    
    def __init__(self, logic: str):
        super().__init__()
        self.logic = logic

    def to_json(self) -> dict: # type: ignore
        return {
            "command": "set-logic", # type: ignore
            "symbol": self.logic # type: ignore
        }


class MCILDefineSystem(MCILCommand):
    
    def __init__(
        self, 
        symbol: str,
        input: list[MCILVar], 
        output: list[MCILVar], 
        local: list[MCILVar], 
        init: MCILExpr,
        trans: MCILExpr, 
        inv: MCILExpr,
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
        self.subsystems: dict[str, MCILDefineSystem] = {}

    def get_exprs(self) -> list[MCILExpr]:
        return [self.init, self.trans, self.inv]

    def __str__(self) -> str:
        input_str = " ".join([f"({i.symbol} {i.sort})" for i in self.input])
        output_str = " ".join([f"({o.symbol} {o.sort})" for o in self.output])
        local_str = " ".join([f"({l.symbol} {l.sort})" for l in self.local])

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

    def to_json(self) -> dict: # type: ignore
        return {
            "command": "define-system", # type: ignore
            "symbol": self.symbol, # type: ignore
            "input": [i.to_json_sorted_var() for i in self.input], # type: ignore
            "output": [o.to_json_sorted_var() for o in self.output], # type: ignore
            "local": [l.to_json_sorted_var() for l in self.local], # type: ignore
            "init": self.init.to_json(), # type: ignore
            "trans": self.trans.to_json(), # type: ignore
            "inv": self.inv.to_json(), # type: ignore
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


class MCILCheckSystem(MCILCommand):
    
    def __init__(
        self, 
        sys_symbol: str,
        input: list[MCILVar], 
        output: list[MCILVar], 
        local: list[MCILVar], 
        assumption: dict[str, MCILExpr],
        fairness: dict[str, MCILExpr], 
        reachable: dict[str, MCILExpr], 
        current: dict[str, MCILExpr], 
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

    def get_exprs(self) -> list[MCILExpr]:
        return [a for a in self.assumption.values()] + [f for f in self.fairness.values()] + [r for r in self.reachable.values()] + [c for c in self.current.values()]

    def __str__(self) -> str:
        input_str = " ".join([f"({i.symbol} {i.sort})" for i in self.input])
        output_str = " ".join([f"({o.symbol} {o.sort})" for o in self.output])
        local_str = " ".join([f"({l.symbol} {l.sort})" for l in self.local])

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

    def to_json(self) -> dict: # type: ignore
        return { # type: ignore
            "command": "check-system",
            "symbol": self.sys_symbol,
            "input": [i.to_json_sorted_var() for i in self.input], # type: ignore
            "output": [o.to_json_sorted_var() for o in self.output], # type: ignore
            "local": [l.to_json_sorted_var() for l in self.local],# type: ignore
            "assumption": [{"symbol": s, "formula": a.to_json()} for s,a in self.assumption.items()], # type: ignore
            "fairness": [{"symbol": s, "formula": f.to_json()} for s,f in self.fairness.items()], # type: ignore
            "reachable": [{"symbol": s, "formula": r.to_json()} for s,r in self.reachable.items()], # type: ignore
            "current": [{"symbol": s, "formula": c.to_json()} for s,c in self.current.items()], # type: ignore
            "query": [{"symbol": s, "formulas": q} for s,q in self.query.items()],
            "queries": []
        }


class MCILProgram():

    def __init__(self, commands: list[MCILCommand]):
        self.commands: list[MCILCommand] = commands

    def get_check_system_cmds(self) -> list[MCILCheckSystem]:
        return [cmd for cmd in self.commands if isinstance(cmd, MCILCheckSystem)]

    def __str__(self) -> str:
        return "\n".join(str(cmd) for cmd in self.commands)

    def to_json(self) -> list: # type: ignore
        return [cmd.to_json() for cmd in self.commands] # type: ignore


class MCILExit(MCILCommand):
    pass


MCIL_BOOL_EXPR = lambda x: MCILConstant(MCIL_BOOL_SORT, x) # type: ignore
MCIL_EQ_EXPR = lambda x,y: MCILApply(MCIL_BOOL_SORT, MCILIdentifier("=", []), [x,y]) # type: ignore


# A rank is a function signature. For example:
#   rank(and) = ([Bool, Bool], Bool)
Rank = tuple[list[MCILSort], MCILSort]

# An identifier class describes a class of identifiers that have the same symbol and number of indices.
# For instance, ("BitVec", 1) describes the class of bit vector sorts and ("extract", 2) describes the 
# class of all bit vector "extract" operators.
IdentifierClass = tuple[str, int]

# RankTable[f,i] = ( par A ( rank(f,A) ) )
#   where rank(f,A) is the rank of function with symbol f and number indices i given parameter(s) A
RankTable = dict[IdentifierClass, Callable[[Any], Rank]]

CORE_RANK_TABLE: RankTable = {
    ("true", 0):     lambda _: ([], MCIL_BOOL_SORT),
    ("false", 0):    lambda _: ([], MCIL_BOOL_SORT),
    ("not", 0):      lambda _: ([MCIL_BOOL_SORT], MCIL_BOOL_SORT),
    ("=>", 0):       lambda _: ([MCIL_BOOL_SORT, MCIL_BOOL_SORT], MCIL_BOOL_SORT),
    ("and", 0):      lambda _: ([MCIL_BOOL_SORT, MCIL_BOOL_SORT], MCIL_BOOL_SORT),
    ("or", 0):       lambda _: ([MCIL_BOOL_SORT, MCIL_BOOL_SORT], MCIL_BOOL_SORT),
    ("xor", 0):      lambda _: ([MCIL_BOOL_SORT, MCIL_BOOL_SORT], MCIL_BOOL_SORT),
    ("=", 0):        lambda A: ([A,A], MCIL_BOOL_SORT),
    ("distinct", 0): lambda A: ([A,A], MCIL_BOOL_SORT),
    ("ite", 0):      lambda A: ([MCIL_BOOL_SORT, A, A], A),
}

BITVEC_RANK_TABLE: RankTable = {
    ("concat", 0):       lambda A: ([MCIL_BITVEC_SORT(A[0]), MCIL_BITVEC_SORT(A[1])], MCIL_BITVEC_SORT(A[0]+A[1])),
    ("extract", 2):      lambda A: ([MCIL_BITVEC_SORT(A[0])], MCIL_BITVEC_SORT(A[1])),
    ("zero_extend", 1):  lambda A: ([MCIL_BITVEC_SORT(A[0])], MCIL_BITVEC_SORT(A[0] + A[1])),
    ("sign_extend", 1):  lambda A: ([MCIL_BITVEC_SORT(A[0])], MCIL_BITVEC_SORT(A[0] + A[1])),
    ("rotate_left", 1):  lambda A: ([MCIL_BITVEC_SORT(A)], MCIL_BITVEC_SORT(A)),
    ("rotate_right", 1): lambda A: ([MCIL_BITVEC_SORT(A)], MCIL_BITVEC_SORT(A)),
    ("bvshl", 0):  lambda A: ([MCIL_BITVEC_SORT(A), MCIL_BITVEC_SORT(A)], MCIL_BITVEC_SORT(A)),
    ("bvlshr", 0): lambda A: ([MCIL_BITVEC_SORT(A), MCIL_BITVEC_SORT(A)], MCIL_BITVEC_SORT(A)),
    ("bvashr", 0): lambda A: ([MCIL_BITVEC_SORT(A), MCIL_BITVEC_SORT(A)], MCIL_BITVEC_SORT(A)),
    ("bvnot", 0):  lambda A: ([MCIL_BITVEC_SORT(A)], MCIL_BITVEC_SORT(A)),
    ("bvneg", 0):  lambda A: ([MCIL_BITVEC_SORT(A)], MCIL_BITVEC_SORT(A)),
    ("bvand", 0):  lambda A: ([MCIL_BITVEC_SORT(A), MCIL_BITVEC_SORT(A)], MCIL_BITVEC_SORT(A)),
    ("bvnand", 0): lambda A: ([MCIL_BITVEC_SORT(A), MCIL_BITVEC_SORT(A)], MCIL_BITVEC_SORT(A)),
    ("bvor", 0):   lambda A: ([MCIL_BITVEC_SORT(A), MCIL_BITVEC_SORT(A)], MCIL_BITVEC_SORT(A)),
    ("bvnor", 0):  lambda A: ([MCIL_BITVEC_SORT(A), MCIL_BITVEC_SORT(A)], MCIL_BITVEC_SORT(A)),
    ("bvxor", 0):  lambda A: ([MCIL_BITVEC_SORT(A), MCIL_BITVEC_SORT(A)], MCIL_BITVEC_SORT(A)),
    ("bvxnor", 0): lambda A: ([MCIL_BITVEC_SORT(A), MCIL_BITVEC_SORT(A)], MCIL_BITVEC_SORT(A)),
    ("bvadd", 0):  lambda A: ([MCIL_BITVEC_SORT(A), MCIL_BITVEC_SORT(A)], MCIL_BITVEC_SORT(A)), 
    ("bvsub", 0):  lambda A: ([MCIL_BITVEC_SORT(A), MCIL_BITVEC_SORT(A)], MCIL_BITVEC_SORT(A)),
    ("bvmul", 0):  lambda A: ([MCIL_BITVEC_SORT(A), MCIL_BITVEC_SORT(A)], MCIL_BITVEC_SORT(A)),
    ("bvudiv", 0): lambda A: ([MCIL_BITVEC_SORT(A), MCIL_BITVEC_SORT(A)], MCIL_BITVEC_SORT(A)),
    ("bvsdiv", 0): lambda A: ([MCIL_BITVEC_SORT(A), MCIL_BITVEC_SORT(A)], MCIL_BITVEC_SORT(A)),
    ("bvurem", 0): lambda A: ([MCIL_BITVEC_SORT(A), MCIL_BITVEC_SORT(A)], MCIL_BITVEC_SORT(A)),
    ("bvsrem", 0): lambda A: ([MCIL_BITVEC_SORT(A), MCIL_BITVEC_SORT(A)], MCIL_BITVEC_SORT(A)),
    ("bvsmod", 0): lambda A: ([MCIL_BITVEC_SORT(A), MCIL_BITVEC_SORT(A)], MCIL_BITVEC_SORT(A)),
    ("bvult", 0):  lambda A: ([MCIL_BITVEC_SORT(A), MCIL_BITVEC_SORT(A)], MCIL_BOOL_SORT),
    ("bvule", 0):  lambda A: ([MCIL_BITVEC_SORT(A), MCIL_BITVEC_SORT(A)], MCIL_BOOL_SORT),
    ("bvugt", 0):  lambda A: ([MCIL_BITVEC_SORT(A), MCIL_BITVEC_SORT(A)], MCIL_BOOL_SORT),
    ("bvuge", 0):  lambda A: ([MCIL_BITVEC_SORT(A), MCIL_BITVEC_SORT(A)], MCIL_BOOL_SORT),
    ("bvslt", 0):  lambda A: ([MCIL_BITVEC_SORT(A), MCIL_BITVEC_SORT(A)], MCIL_BOOL_SORT),
    ("bvsle", 0):  lambda A: ([MCIL_BITVEC_SORT(A), MCIL_BITVEC_SORT(A)], MCIL_BOOL_SORT),
    ("bvsgt", 0):  lambda A: ([MCIL_BITVEC_SORT(A), MCIL_BITVEC_SORT(A)], MCIL_BOOL_SORT),
    ("bvsge", 0):  lambda A: ([MCIL_BITVEC_SORT(A), MCIL_BITVEC_SORT(A)], MCIL_BOOL_SORT),
    ("reduce_and", 0): lambda A: ([MCIL_BITVEC_SORT(A)], MCIL_BOOL_SORT),
    ("reduce_or", 0):  lambda A: ([MCIL_BITVEC_SORT(A)], MCIL_BOOL_SORT),
    ("reduce_xor", 0): lambda A: ([MCIL_BITVEC_SORT(A)], MCIL_BOOL_SORT)
}

ARRAY_RANK_TABLE: RankTable = {
    ("select", 0): lambda A: ([MCIL_ARRAY_SORT(A[0], A[1]), A[0]], A[1]),
    ("store", 0):  lambda A: ([MCIL_ARRAY_SORT(A[0], A[1]), A[0], A[1]], MCIL_ARRAY_SORT(A[0], A[1]))
}


def sort_check_apply_rank(node: MCILApply, rank: Rank) -> bool:
    rank_args, rank_return = rank
    if rank_args != [c.sort for c in node.children]:
        return False

    node.sort = rank_return
    return True


def sort_check_apply_core(node: MCILApply) -> bool:
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


def sort_check_apply_bitvec(node: MCILApply) -> bool:
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
        operand2 = node.children[1]
        if not operand1.sort.identifier.is_indexed():
            return False
        elif not operand2.sort.identifier.is_indexed():
            return False

        i = operand1.sort.identifier.indices[0]
        j = operand2.sort.identifier.indices[0]
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

        if j > i or i >= m:
            return False

        n = i - j + 1
        if n < 1:
            return False

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


def sort_check_apply_arrays(node: MCILApply) -> bool:
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


def sort_check_apply_qf_bv(node: MCILApply) -> bool:
    identifier_class = (node.identifier.symbol, node.identifier.num_indices())

    if identifier_class in CORE_RANK_TABLE:
        return sort_check_apply_core(node)
    elif identifier_class in BITVEC_RANK_TABLE:
        return sort_check_apply_bitvec(node)

    return False


def sort_check_apply_qf_abv(node: MCILApply) -> bool:
    identifier_class = (node.identifier.symbol, node.identifier.num_indices())

    if identifier_class in CORE_RANK_TABLE:
        return sort_check_apply_core(node)
    elif identifier_class in BITVEC_RANK_TABLE:
        return sort_check_apply_bitvec(node)
    elif identifier_class in ARRAY_RANK_TABLE:
        return sort_check_apply_arrays(node)
    
    return False


class MCILLogic():
    """An ILLogic has a name, a set of sort symbols, a set of function symbols, and a sort_check function"""

    def __init__(
        self, 
        symbol: str, 
        sort_symbols: set[IdentifierClass],
        function_symbols: set[IdentifierClass],
        sort_check: Callable[[MCILApply], bool]
    ):
        self.symbol = symbol
        self.sort_symbols = sort_symbols
        self.function_symbols = function_symbols
        self.sort_check = sort_check

        self.symbols = sort_symbols | function_symbols


QF_BV = MCILLogic("QF_BV", 
                {("BitVec", 1)}, 
                CORE_RANK_TABLE.keys() | BITVEC_RANK_TABLE.keys(), 
                sort_check_apply_qf_bv)

QF_ABV = MCILLogic("QF_ABV", 
                {("BitVec", 1), ("Array", 0)}, 
                CORE_RANK_TABLE.keys() | BITVEC_RANK_TABLE.keys() | ARRAY_RANK_TABLE.keys(), 
                sort_check_apply_qf_abv)


class MCILSystemContext():

    def __init__(self):
        self._system_stack: list[tuple[str, MCILDefineSystem]] = []

    def push(self, sys: tuple[str, MCILDefineSystem]):
        self._system_stack.append(sys)

    def pop(self) -> tuple[str, MCILDefineSystem]:
        return self._system_stack.pop()

    def copy(self) -> MCILSystemContext:
        new_system_stack = self._system_stack.copy()
        new = MCILSystemContext()
        for s in new_system_stack:
            new.push(s)
        return new

    def get_top_level(self) -> Optional[tuple[str, MCILDefineSystem]]:
        if len(self._system_stack) == 0:
            return None
        return self._system_stack[0]

    def get_subsystems(self) -> list[tuple[str, MCILDefineSystem]]:
        if len(self._system_stack) < 2:
            return []
        return self._system_stack[1:]

    def get_scope_symbols(self) -> list[str]:
        top_level = self.get_top_level()
        if not top_level:
            return []
        top_level_symbol, top_level_system = top_level # type: ignore
        return [top_level_symbol] + [name for name, sys in self.get_subsystems()] # type: ignore

    def __eq__(self, __o: object) -> bool:
        if not isinstance(__o, MCILSystemContext):
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


class MCILContext():

    def __init__(self):
        self.declared_sorts: dict[MCILIdentifier, int] = {}
        self.declared_enum_sorts: dict[str, list[str]] = {}
        self.defined_sorts: set[MCILSort] = set()
        self.declared_functions: dict[str, Rank] = {}
        self.defined_functions: dict[str, tuple[Rank, MCILExpr]] = {}
        self.defined_systems: dict[str, MCILDefineSystem] = {}
        self.logic = QF_ABV # for now, assume QF_BV logic
        self.input_var_sorts: dict[MCILVar, MCILSort] = {}
        self.output_var_sorts: dict[MCILVar, MCILSort] = {}
        self.local_var_sorts: dict[MCILVar, MCILSort] = {}
        self.system_context = MCILSystemContext() # used during system flattening
        self.cur_command: Optional[MCILCommand] = None

    def get_symbols(self) -> set[str]:
        # TODO: this is computed EVERY time, optimize this
        # need to implement setters/update functions for each data structure
        symbols: set[str] = set()

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


def postorder(expr: MCILExpr):
    """Perform an iterative postorder traversal of 'expr', calling 'func' on each node."""
    stack: list[tuple[bool, MCILExpr]] = []
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
        for child in cur.children:
            stack.append((False, child))


def sort_check(program: MCILProgram) -> tuple[bool, MCILContext]:
    context: MCILContext = MCILContext()
    status: bool = True

    def sort_check_expr(node: MCILExpr, no_prime: bool) -> bool:
        """Return true if node is well-sorted where 'no_prime' is true if primed variables are disabled and 'prime_input' is true if input variable are allowed to be primed (true for check-system assumptions and reachability conditions). """
        nonlocal context

        if isinstance(node, MCILConstant):
            return True
        elif isinstance(node, MCILVar) and node in context.input_var_sorts:
            node.var_type = MCILVarType.INPUT
            node.sort = context.input_var_sorts[node]

            if node.prime and no_prime:
                eprint(f"[{__name__}] Error: primed variables only allowed in system transition or invariant relation ({node.symbol}).\n\t{context.cur_command}\n")
                return False

            return True
        elif isinstance(node, MCILVar) and node in context.output_var_sorts:
            node.var_type = MCILVarType.OUTPUT
            node.sort = context.output_var_sorts[node]

            if node.prime and no_prime:
                eprint(f"[{__name__}] Error: primed variables only allowed in system transition or invariant relation ({node.symbol}).\n\t{context.cur_command}\n")
                return False

            return True
        elif isinstance(node, MCILVar) and node in context.local_var_sorts:
            node.var_type = MCILVarType.LOCAL
            node.sort = context.local_var_sorts[node]

            if node.prime and no_prime:
                eprint(f"[{__name__}] Error: primed variables only allowed in system transition or invariant relation ({node.symbol}).\n\t{context.cur_command}\n")
                return False

            return True
        elif isinstance(node, MCILVar):
            eprint(f"[{__name__}] Error: symbol `{node.symbol}` not declared.\n\t{context.cur_command}\n")
            return False
        elif isinstance(node, MCILApply):
            if node.identifier.get_class() in context.logic.function_symbols:
                for arg in node.children:
                    sort_check_expr(arg, no_prime)

                if not context.logic.sort_check(node):
                    eprint(f"[{__name__}] Error: function signature does not match definition.\n\t{node}\n\t{node.identifier} {[str(a.sort) for a in node.children]}\n")
                    return False
            elif node.identifier.symbol in context.defined_functions:
                (rank, _) = context.defined_functions[node.identifier.symbol]

                if not sort_check_apply_rank(node, rank):
                    eprint(f"[{__name__}] Error: function call does not match definition.\n\t{node}\n\t{node.identifier} {[str(a.sort) for a in node.children]}\n")
                    return False
            else:
                eprint(f"[{__name__}] Error: symbol '{node.identifier.symbol}' not recognized ({node}).\n\t{context.cur_command}\n")
                return False

            return True
        else:
            eprint(f"[{__name__}] Error: node type '{node.__class__}' not recognized ({node}).\n\t{context.cur_command}\n")
            return False
    # end sort_check_expr

    for cmd in program.commands:
        context.cur_command = cmd

        if isinstance(cmd, MCILDeclareSort):
            # TODO: move this warning to il2btor.py
            eprint(f"[{__name__}] Warning: declare-sort command unsupported, ignoring.\n")
        elif isinstance(cmd, MCILDefineSort):
            if cmd.symbol in context.get_symbols():
                eprint(f"[{__name__}] Error: symbol '{cmd.symbol}' already in use.\n\t{cmd}\n")
                status = False

            # TODO
        elif isinstance(cmd, MCILDeclareEnumSort):
            if cmd.symbol in context.get_symbols():
                eprint(f"[{__name__}] Error: symbol '{cmd.symbol}' already in use.\n\t{cmd}\n")
                status = False

            context.declared_enum_sorts[cmd.symbol] = cmd.values
        elif isinstance(cmd, MCILDeclareConst):
            if cmd.symbol in context.get_symbols():
                eprint(f"[{__name__}] Error: symbol '{cmd.symbol}' already in use.\n\t{cmd}\n")
                status = False

            context.declared_functions[cmd.symbol] = Rank(([], cmd.sort))
        elif isinstance(cmd, MCILDeclareFun):
            if cmd.symbol in context.get_symbols():
                eprint(f"[{__name__}] Error: symbol '{cmd.symbol}' already in use.\n\t{cmd}\n")
                status = False

            context.declared_functions[cmd.symbol] = Rank((cmd.inputs, cmd.output_sort))
        elif isinstance(cmd, MCILDefineFun):
            if cmd.symbol in context.get_symbols():
                eprint(f"[{__name__}] Error: symbol '{cmd.symbol}' already in use.\n\t{cmd}\n")
                status = False

            input_sorts = [s.sort for s in cmd.inputs]
            context.defined_functions[cmd.symbol] = (Rank((input_sorts, cmd.output_sort)), cmd.body)
        elif isinstance(cmd, MCILDefineSystem):
            # TODO: check for variable name clashes across cmd.input, cmd.output, cmd.local
            # TODO: check for valid sort symbols
            context.input_var_sorts = {var:var.sort for var in cmd.input}
            context.output_var_sorts = {var:var.sort for var in cmd.output}
            context.local_var_sorts = {var:var.sort for var in cmd.local}

            status = status and sort_check_expr(cmd.init, True)
            status = status and sort_check_expr(cmd.trans, False)
            status = status and sort_check_expr(cmd.inv, False)

            for name,subsystem in cmd.subsystem_signatures.items():
                # TODO: check for cycles in system dependency graph
                (sys_symbol, signature_symbols) = subsystem

                if sys_symbol not in context.defined_systems:
                    eprint(f"[{__name__}] Error: system '{sys_symbol}' not defined in context.\n\t{cmd}\n")
                    status = False
                    return (False, context)

                # check that each symbol in signature is in the context
                signature: list[MCILVar] = []
                variables: dict[str, MCILVar] = {var.symbol:var for var in cmd.input + cmd.output + cmd.local}
                for symbol in signature_symbols:
                    if symbol not in variables:
                        eprint(f"[{__name__}] Error: variable '{symbol}' not declared.\n\t{cmd}\n")
                        status = False
                        signature.append(MCIL_EMPTY_VAR)
                        continue

                    signature.append(variables[symbol])
                    if variables[symbol] in cmd.input:
                        variables[symbol].var_type = MCILVarType.INPUT
                    elif variables[symbol] in cmd.output:
                        variables[symbol].var_type = MCILVarType.OUTPUT
                    elif variables[symbol] in cmd.local:
                        variables[symbol].var_type = MCILVarType.LOCAL

                target_system = context.defined_systems[sys_symbol]
                target_signature = target_system.input + target_system.output

                if len(signature) != len(target_signature):
                    eprint(f"[{__name__}] Error: subsystem signature does not match target system ({sys_symbol}).\n\t{context.defined_systems[sys_symbol].input + context.defined_systems[sys_symbol].output}\n\t{signature}\n")
                    status = False
                    continue

                for cmd_var,target_var in zip(signature, target_signature):
                    if cmd_var.sort != target_var.sort:
                        eprint(f"[{__name__}] Error: subsystem signature does not match target system ({sys_symbol}).\n\t{context.defined_systems[sys_symbol].input + context.defined_systems[sys_symbol].output}\n\t{signature}\n")
                        status = False
                        continue

                cmd.subsystems[name] = context.defined_systems[sys_symbol]

            context.defined_systems[cmd.symbol] = cmd

            context.input_var_sorts = {}
            context.output_var_sorts = {}
            context.local_var_sorts = {}
        elif isinstance(cmd, MCILCheckSystem):
            if not cmd.sys_symbol in context.defined_systems:
                eprint(f"[{__name__}] Error: system '{cmd.sys_symbol}' undefined.\n\t{cmd}\n")
                status = False
                continue

            context.input_var_sorts = {var:var.sort for var in cmd.input}
            context.output_var_sorts = {var:var.sort for var in cmd.output}
            context.local_var_sorts = {var:var.sort for var in cmd.local}

            system = context.defined_systems[cmd.sys_symbol]

            if len(system.input) != len(cmd.input):
                eprint(f"[{__name__}] Error: input variables do not match target system ({system.symbol}).\n\t{system.input}\n\t{cmd.input}\n")
                status = False
                continue

            for i1,i2 in zip(system.input, cmd.input):
                if i1.sort != i2.sort:
                    eprint(f"[{__name__}] Error: sorts do not match in check-system (expected {i1.sort}, got {i2.sort})\n")
                    status = False
                else:
                    i2.var_type = MCILVarType.INPUT
                # cmd.rename_map[v1] = v2

            if len(system.output) != len(cmd.output):
                eprint(f"[{__name__}] Error: output variables do not match target system ({system.symbol}).\n\t{system.output}\n\t{cmd.output}\n")
                status = False
                continue

            for o1,o2 in zip(system.output, cmd.output):
                if o1.sort != o2.sort:
                    eprint(f"[{__name__}] Error: sorts do not match in check-system (expected {o1.sort}, got {o2.sort})\n")
                    status = False
                else:
                    o2.var_type = MCILVarType.OUTPUT
                # cmd.rename_map[v1] = v2

            if len(system.local) != len(cmd.local):
                eprint(f"[{__name__}] Error: local variables do not match target system ({system.symbol}).\n\tlen(define.local)={len(system.local)}\n\tlen(check.local)={len(cmd.local)}\n")
                status = False
                continue

            for l1,l2 in zip(system.local, cmd.local):
                if l1.sort != l2.sort:
                    eprint(f"[{__name__}] Error: sorts do not match in check-system (expected {l1.sort}, got {l2.sort})\n")
                    status = False
                else:
                    l2.var_type = MCILVarType.LOCAL
                # cmd.rename_map[v1] = v2

            for expr in cmd.assumption.values():
                status = status and sort_check_expr(expr, False)

            for expr in cmd.reachable.values():
                status = status and sort_check_expr(expr, False)

            for expr in cmd.fairness.values():
                status = status and sort_check_expr(expr, False)

            for expr in cmd.current.values():
                status = status and sort_check_expr(expr, False)

            context.input_var_sorts = {}
            context.output_var_sorts = {}
            context.local_var_sorts = {}
        else:
            raise NotImplementedError

    return (status, context)


def to_qfbv(program: MCILProgram):

    SORT_MAP = {
        "Int": MCIL_BITVEC_SORT(64)
    }

    OPERATOR_MAP = {
        "+": MCILIdentifier("bvadd", []),
        "-": MCILIdentifier("bvsub", []),
        "*": MCILIdentifier("bvmul", []),
        "%": MCILIdentifier("bvsmod", []),
        "/": MCILIdentifier("bvsdiv", []),
        ">": MCILIdentifier("bvsgt", []),
        "<": MCILIdentifier("bvslt", []),
        ">=": MCILIdentifier("bvsge", []),
        "<=": MCILIdentifier("bvsle", [])
    }

    def to_qfbv_expr(expr: MCILExpr):
        if isinstance(expr, MCILApply) and expr.identifier.symbol in OPERATOR_MAP:
            expr.identifier = OPERATOR_MAP[expr.identifier.symbol]
            
        if expr.sort.identifier.symbol in SORT_MAP:
            expr.sort = SORT_MAP[expr.sort.identifier.symbol]

    for command in program.commands:
        if isinstance(command, MCILDefineSort):
            # FIXME: Need to check for any Int parameters of the definition
            raise NotImplementedError
        elif isinstance(command, MCILDeclareConst) and command.sort.identifier.symbol in SORT_MAP:
            command.sort = SORT_MAP[command.sort.identifier.symbol]
        elif isinstance(command, MCILDeclareFun):
            for ivar in [i for i in command.inputs if i.identifier.symbol in SORT_MAP]:
                command.inputs[command.inputs.index(ivar)] = SORT_MAP[ivar.identifier.symbol]

            if command.output_sort.identifier.symbol in SORT_MAP:
                command.output_sort = SORT_MAP[command.output_sort.identifier.symbol]
        elif isinstance(command, MCILDefineFun):
            for ivar in [i for i in command.inputs if i.sort.identifier.symbol in SORT_MAP]:
                command.inputs[command.inputs.index(ivar)].sort = SORT_MAP[ivar.sort.identifier.symbol]

            if command.output_sort.identifier.symbol in SORT_MAP:
                command.output_sort = SORT_MAP[command.output_sort.identifier.symbol]
        elif isinstance(command, MCILDefineSystem):
            for var in [v for v in command.input if v.sort.identifier.symbol in SORT_MAP]:
                command.input[command.input.index(var)].sort = SORT_MAP[var.sort.identifier.symbol]
            for var in [v for v in command.output if v.sort.identifier.symbol in SORT_MAP]:
                command.output[command.output.index(var)].sort = SORT_MAP[var.sort.identifier.symbol]
            for var in [v for v in command.local if v.sort.identifier.symbol in SORT_MAP]:
                command.local[command.local.index(var)].sort = SORT_MAP[var.sort.identifier.symbol]

        for expr1 in command.get_exprs():
            for expr2 in postorder(expr1):
                to_qfbv_expr(expr2)

