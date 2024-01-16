"""
Representation of IL
"""
from __future__ import annotations

from pathlib import Path
from collections import deque
from copy import copy
from enum import Enum
from typing import Any, Callable, Optional, cast

from .util import logger

FILE_NAME = Path(__file__).name

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
    QUERIES    = ":queries"

    def is_variable_declaration(self) -> bool:
        return self.value == ":input" or self.value == ":output" or self.value == ":local"

    def is_definable_once(self) -> bool:
        return self.is_variable_declaration() or self.value == ":init"

    def get_value_type(self) -> type:
        if self.value == ":input" or self.value == ":output" or self.value == ":local" or self.value == ":subsys" or self.value == ":assumption" or self.value == ":fairness" or self.value == ":reachable" or self.value == ":current" or self.value == ":query":
            return dict
        elif self.value == ":queries":
            return list
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

    def check(self, __symbols: set[str], num_indices: int) -> bool:
        """Returns true if this has `num_indices` and any of the symbols listed in `__symbols`"""
        return any([self.symbol == s for s in __symbols]) and len(self.indices) == num_indices

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

    
    def to_json(self) -> dict:
        return {"symbol": self.symbol, "indices": self.indices}


class MCILSort():

    def __init__(self, identifier: MCILIdentifier, sorts: list[MCILSort]):
        self.identifier = identifier
        self.symbol = identifier.symbol
        self.parameters = sorts

    def arity(self) -> int:
        return len(self.parameters)

    def is_parametric(self) -> bool:
        return len(self.parameters) > 0 

    def get_index(self, index: int) -> int:
        return self.identifier.indices[index]

    def __eq__(self, __value: object) -> bool:
        if not isinstance(__value, MCILSort):
            return False

        if is_any_sort(self) or is_any_sort(__value):
            return True
        
        if is_bool_sort(self) and is_bool_sort(__value):
            return True
        
        if is_bool_sort(self) and is_bitvec_sort(__value) and __value.identifier.indices[0] == 1:
            return True

        if is_bool_sort(__value) and is_bitvec_sort(self) and self.identifier.indices[0] == 1:
            return True

        if self.identifier != __value.identifier:
            return False

        if [s for s in self.parameters] != [s for s in __value.parameters]:
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

    def to_json(self) -> dict:
        identifier = self.identifier.to_json()
        parameters = [s.to_json() for s in self.parameters]
        return {"identifier": identifier, "parameters": parameters}


# Built-in sorts
MCIL_NO_SORT: MCILSort = MCILSort(MCILIdentifier("", []), []) # placeholder sort
MCIL_BOOL_SORT: MCILSort = MCILSort(MCILIdentifier("Bool", []), [])
MCIL_INT_SORT: MCILSort = MCILSort(MCILIdentifier("Int", []), [])
MCIL_BITVEC_SORT: Callable[[int], MCILSort] = lambda n: MCILSort(MCILIdentifier("BitVec", [n]), [])
MCIL_ARRAY_SORT: Callable[[MCILSort, MCILSort], MCILSort] = lambda A,B: MCILSort(MCILIdentifier("Array", []), [A,B])
MCIL_ENUM_SORT:  Callable[[str], MCILSort] = lambda s: MCILSort(MCILIdentifier(s, []), [])
MCIL_ANY_SORT: MCILSort = MCILSort(MCILIdentifier("__Any__", []), [])


def is_bool_sort(sort: MCILSort) -> bool:
    """A Bool sort has an identifier that is the symbol 'Bool' and is non-parametric"""
    return sort.identifier.is_symbol("Bool") and not sort.is_parametric()

def is_bitvec_sort(sort: MCILSort) -> bool:
    """A bit vector sort has an identifier with the symbol 'BitVec' and is indexed with a single numeral"""
    return (sort.symbol == "BitVec" and len(sort.identifier.indices) == 1)

def is_int_sort(sort: MCILSort) -> bool:
    """An Int sort has an identifier that is the symbol 'Int' and is non-parametric"""
    return sort.identifier.is_symbol("Int") and not sort.is_parametric()

def is_array_sort(sort: MCILSort) -> bool:
    """An Array sort has an identifier that is the symbol 'Array' and has two parameters"""
    return sort.identifier.is_symbol("Array") and sort.arity() == 2
    
def is_any_sort(sort: MCILSort) -> bool:
    """An Any sort has an identifier that is the symbol '__Any__'"""
    return sort.identifier.is_symbol("__Any__")


class MCILExpr():

    def __init__(self, sort: MCILSort, children: list[MCILExpr]):
        self.sort = sort
        self.children = children

        self.field: Optional[tuple[MCILCommand, str, str]] = None

        self.parents: list[MCILExpr] = []
        for child in children:
            child.parents.append(self)

    def get_sort_symbol(self) -> str:
        return self.sort.symbol

    def replace(self, new: MCILExpr) -> None:
        """Replaces `self` with `new` using `self.parents` or `self.field` if `self` is a top-level expression (i.e., has no parents)."""
        if not self.parents:
            if not self.field:
                raise ValueError(f"No field set for top-level expression '{self}'")

            cmd,field_name,symbol = self.field
            cmd_field = getattr(cmd, field_name)

            if isinstance(cmd_field, MCILExpr):
                setattr(cmd, field_name, new)
            elif isinstance(cmd_field, dict):
                cmd_field[symbol] = new

        for parent in self.parents:
            parent.children[parent.children.index(self)] = new
            new.parents.append(parent)

    def __hash__(self) -> int:
        return id(self)

    def __str__(self) -> str:
        return mcil2str(self)

    def to_json(self) -> dict:
        return {}


class MCILConstant(MCILExpr):

    def __init__(self, sort: MCILSort, value: Any):
        super().__init__(sort, [])
        self.value = value

    def to_json(self) -> dict:
        return {"identifier": str(self)}


class MCILVarType(Enum):
    NONE   = 0
    INPUT  = 1,
    OUTPUT = 2,
    LOCAL  = 3,
    LOGIC  = 4


class MCILVar(MCILExpr):
    """An ILVar requires a sort and symbol."""

    def __init__(self, sort: MCILSort, symbol: str, prime: bool):
        super().__init__(sort, [])
        # self.var_type = var_type
        self.symbol = symbol
        self.prime = prime

    def __eq__(self, __value: object) -> bool:
        """Two ILVars are equal if they have the same symbol."""
        return (isinstance(__value, MCILVar) 
            and self.symbol != __value.symbol 
            and self.prime == __value.prime)
            # and self.var_type != __value.var_type)

    def __hash__(self) -> int:
        return hash(self.symbol)

    def to_json(self) -> dict:
        return {"identifier": self.symbol + ("'" if self.prime else "")}

    def to_json_sorted_var(self) -> dict:
        return {"symbol": self.symbol, "sort": self.sort.to_json()}


MCIL_EMPTY_VAR = MCILVar(MCIL_NO_SORT, "", False)


class MCILApply(MCILExpr):

    def __init__(
        self, 
        sort: MCILSort, 
        identifier: MCILIdentifier, 
        children: list[MCILExpr]
    ):
        super().__init__(sort, children)
        self.identifier = identifier

    def to_json(self) -> dict:
        identifier = self.identifier.to_json()
        args = [c.to_json() for c in self.children]
        return {"identifier": identifier, "args": args}


class MCILLetExpr(MCILExpr):
    """MCILLetExpr tree structure looks like:
    
    MCILLetExpr
    ____|___________________________
    |        |        |            |
    v        v        v            v  
    MCILExpr MCILBind MCILExpr ... MCILExpr

    where from the right we have each bound variable expression, then a dummy class to do variable binding during traversal, then the argument expression. We visit these in that order when performing the standard reverse postorder traversal.
    """

    def __init__(
        self, 
        sort: MCILSort, 
        binders: list[tuple[str, MCILExpr]],
        expr: MCILExpr
    ):
        super().__init__(sort, [expr] + [MCILBind()] + [b[1] for b in binders])
        self.vars = [b[0] for b in binders]

    def get_expr(self) -> MCILExpr:
        return self.children[0]

    def get_binders(self) -> list[tuple[str, MCILExpr]]:
        return [(v,e) for v,e in zip(self.vars, self.children[2:])]


class MCILBind(MCILExpr):
    """Class used for binding variables in `let` expressions during traversal."""

    def __init__(self):
        super().__init__(MCIL_NO_SORT, [])

    def get_binders(self) -> list[tuple[str, MCILExpr]]:
        if not len(self.parents) == 1:
            raise ValueError(f"MCILBind can only have 1 parent.")

        parent = self.parents[0]

        if not isinstance(parent, MCILLetExpr):
            raise ValueError(f"MCILBind must have MCILLetExpr parent.")

        return parent.get_binders()


def mcil2str(expr: MCILExpr) -> str:
    queue: deque[tuple[bool, MCILExpr|tuple[str,MCILExpr]]] = deque()
    s = ""

    queue.append((False, expr))

    while len(queue) > 0:
        (handled, cur) = queue.pop()

        if handled:
            s = (s[:-1] + ") ") if isinstance(cur, (MCILApply, MCILLetExpr, tuple)) else s
            continue

        # first time seeing this node
        if isinstance(cur, MCILApply) and cur.identifier.is_symbol("const"):
            s += f"((as {cur.identifier} {cur.sort}) "
        elif isinstance(cur, MCILApply):
            s += f"({cur.identifier} "
        elif isinstance(cur, MCILLetExpr):
            s += f"(let ("
        elif isinstance(cur, MCILBind):
            s = s[:-1] + ") "
        elif isinstance(cur, MCILConstant) and is_bitvec_sort(cur.sort):
            format_str = f"#b{'{'}0:0{cur.sort.identifier.indices[0]}b{'}'} "
            s += format_str.format(cur.value)
        elif isinstance(cur, MCILConstant) and isinstance(cur.value, bool):
            s += str(cur.value).lower() + " "
        elif isinstance(cur, MCILConstant):
            s += f"{cur.value} "
        elif isinstance(cur, MCILVar):
            s += f"{cur.symbol}" + ("' " if cur.prime else " ")
        elif isinstance(cur, tuple):
            (v,e) = cur
            s += f"({v} "
        else:
            s += f"{str(cur)} "

        queue.append((True, cur))

        # add children to stack
        if isinstance(cur, MCILLetExpr):
            queue.append((False, cur.get_expr()))
            queue.append((False, cur.children[1]))
            for v,e in reversed(cur.get_binders()):
                queue.append((False, (v,e)))
        elif isinstance(cur, tuple):
            (_,e) = cur
            queue.append((False, e))
        else:
            for child in reversed(cur.children):
                queue.append((False, child))

    if s[-1] == " ":
        s = s[:-1]

    return s


def rename_vars(expr: MCILExpr, vars: dict[MCILVar, MCILExpr], context: MCILContext) -> MCILExpr:
    """Returns a copy of `expr` where each `MCILVar` present in `vars` is replaced with its mapped value. Useful for inlining function calls."""
    new_expr = copy(expr)

    for subexpr in postorder_mcil(new_expr, context):
        if subexpr in vars:
            subexpr.replace(vars[subexpr])

    return new_expr


def is_const_array_expr(expr: MCILExpr) -> bool:
    """Returns true if `expr` is of the form: `(as const (Array X Y) x)`"""
    return isinstance(expr, MCILApply) and expr.identifier.is_symbol("const") and is_array_sort(expr.sort)


def to_json_sorted_var(symbol: str, sort: MCILSort) -> dict:
    return {"symbol": symbol, "sort": sort.to_json()}


class MCILCommand():

    def get_exprs(self) -> list[MCILExpr]:
        return []

    def to_json(self) -> dict:
        return {}


class MCILDeclareSort(MCILCommand):

    def __init__(self, symbol: str, arity: int):
        super().__init__()
        self.symbol = symbol
        self.arity = arity

    def __str__(self) -> str:
        return f"(declare-sort {self.symbol} {self.arity})"

    def to_json(self) -> dict:
        return {"command": "declare-sort", "symbol": self.symbol, "arity": self.arity}


class MCILDefineSort(MCILCommand):

    def __init__(self, symbol: str, parameters: list[str], definition: MCILSort):
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


class MCILDeclareEnumSort(MCILCommand):

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


class MCILDeclareConst(MCILCommand):

    def __init__(self, symbol: str, sort: MCILSort):
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

    def to_json(self) -> dict:
        return {
            "command": "declare-fun",
            "symbol": self.symbol,
            "inputs": [i.to_json() for i in self.inputs],
            "output": self.output_sort.to_json()
        }


class MCILDefineFun(MCILCommand):

    def __init__(
            self, 
            symbol: str, 
            input: list[tuple[str, MCILSort]], 
            output: MCILSort,  
            body: MCILExpr):
        super().__init__()
        self.symbol = symbol
        self.input = input
        self.output_sort = output
        self.body = body

        self.body.field = (self, "body", "")

    def get_exprs(self) -> list[MCILExpr]:
        return [self.body]

    def __str__(self) -> str:
        input_str = " ".join([f"({symbol} {sort})" for symbol,sort in self.input])
        return f"(define-fun {self.symbol} ({input_str}) {self.output_sort} {self.body})"

    def to_json(self) -> dict:
        return {
            "command": "define-fun",
            "symbol": self.symbol,
            "input": [to_json_sorted_var(symbol,sort) for symbol,sort in self.input],
            "output": self.output_sort.to_json(),
            "body": self.body.to_json()
        }


class MCILSetLogic(MCILCommand):
    
    def __init__(self, logic: str):
        super().__init__()
        self.logic = logic

    def __str__(self) -> str:
        return f"(set-logic {self.logic})"

    def to_json(self) -> dict:
        return {
            "command": "set-logic",
            "logic": self.logic
        }


class MCILSystemCommand(MCILCommand):
    def __init__(
        self,
        symbol: str,
        input: list[tuple[str, MCILSort]], 
        output: list[tuple[str, MCILSort]], 
        local: list[tuple[str, MCILSort]],
    ) -> None:
        self.symbol = symbol
        self.input = input
        self.local = local
        self.output = output

        # this gets populated by sort checker
        self.var_sorts: dict[str, MCILSort] = {}

        # useful for mapping variables across subsystems
        self.input_vars = [MCILVar(sort, symbol, False) for symbol,sort in input]
        self.output_vars = [MCILVar(sort, symbol, False) for symbol,sort in output]
        self.local_vars = [MCILVar(sort, symbol, False) for symbol,sort in local]

        self.input_symbols = set([s for s,_ in self.input])
        self.output_symbols = set([s for s,_ in self.output])
        self.local_symbols = set([s for s,_ in self.local])

    def get_signature(self) -> list[str]:
        """Returns list of input and output variable names. Useful for when instantiating this as a subsystem."""
        return [s for s,_ in self.input] + [s for s,_ in self.output]

    def get_full_signature(self) -> list[str]:
        """Returns list of input, output, and local variable names. Useful for when targeting this system with a check-system command."""
        return [s for s,_ in self.input] + [s for s,_ in self.output] + [s for s,_ in self.local]

    def get_sort(self, symbol: str) -> Optional[MCILSort]:
        """Returns the sort of the variable with symbol `symbol`, if there exists such a variable."""
        if symbol not in self.var_sorts:
            return None
        return self.var_sorts[symbol]


class MCILDefineSystem(MCILSystemCommand):
    
    def __init__(
        self, 
        symbol: str,
        input: list[tuple[str, MCILSort]], 
        output: list[tuple[str, MCILSort]], 
        local: list[tuple[str, MCILSort]], 
        init: MCILExpr,
        trans: MCILExpr, 
        inv: MCILExpr,
        subsystems: dict[str, tuple[str, list[str]]]
    ):
        super().__init__(symbol, input, output, local)
        self.init = init
        self.trans = trans
        self.inv = inv
        self.subsystem_signatures = subsystems

        self.init.field = (self, "init", "")
        self.trans.field = (self, "trans", "")
        self.inv.field = (self, "inv", "")

        # this gets populated by sort checker
        self.subsystems: dict[str, MCILDefineSystem] = {}

    def get_subsys_params(self, symbol: str) -> list[str]:
        return self.subsystem_signatures[symbol][1]

    def get_exprs(self) -> list[MCILExpr]:
        return [self.init, self.trans, self.inv]

    def __str__(self) -> str:
        input_str = " ".join([f"({symbol} {sort})" for symbol,sort in self.input])
        output_str = " ".join([f"({symbol} {sort})" for symbol,sort in self.output])
        local_str = " ".join([f"({symbol} {sort})" for symbol,sort in self.local])

        subsystem_str = ""
        for symbol,signature in self.subsystem_signatures.items():
            (sys_symbol, args) = signature
            subsystem_str += f"\n   :subsys ({symbol} ({sys_symbol} {' '.join(args)}))"

        s =  f"(define-system {self.symbol} "
        s += f"\n   :input ({input_str}) "
        s += f"\n   :output ({output_str}) "
        s += f"\n   :local ({local_str}) "
        s += f"\n   :init {self.init} "
        s += f"\n   :trans {self.trans} "
        s += f"\n   :inv {self.inv} "
        s += subsystem_str

        return s + ")"

    def to_json(self) -> dict:
        return {
            "command": "define-system", 
            "symbol": self.symbol, 
            "input": [to_json_sorted_var(symbol,sort) for symbol,sort in self.input],
            "output": [to_json_sorted_var(symbol,sort) for symbol,sort in self.output], 
            "local": [to_json_sorted_var(symbol,sort) for symbol,sort in self.local], 
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


class MCILCheckSystem(MCILSystemCommand):
    
    def __init__(
        self, 
        symbol: str,
        input: list[tuple[str, MCILSort]], 
        output: list[tuple[str, MCILSort]], 
        local: list[tuple[str, MCILSort]],
        assumption: dict[str, MCILExpr],
        fairness: dict[str, MCILExpr], 
        reachable: dict[str, MCILExpr], 
        current: dict[str, MCILExpr], 
        query: dict[str, list[str]], 
        queries: list[dict[str, list[str]]], 
    ):
        super().__init__(symbol, input, output, local)
        self.assumption = assumption
        self.fairness = fairness
        self.reachable = reachable
        self.current = current
        self.query = query
        self.queries = queries

        for symbol,expr in assumption.items():
            expr.field = (self, "assumption", symbol)
        for symbol,expr in fairness.items():
            expr.field = (self, "fairness", symbol)
        for symbol,expr in reachable.items():
            expr.field = (self, "reachable", symbol)
        for symbol,expr in current.items():
            expr.field = (self, "current", symbol)

    def get_exprs(self) -> list[MCILExpr]:
        return [a for a in self.assumption.values()] + [f for f in self.fairness.values()] + [r for r in self.reachable.values()] + [c for c in self.current.values()]

    def __str__(self) -> str:
        input_str = " ".join([f"({symbol} {sort})" for symbol,sort in self.input])
        output_str = " ".join([f"({symbol} {sort})" for symbol,sort in self.output])
        local_str = " ".join([f"({symbol} {sort})" for symbol,sort in self.local])

        assumption_str = "".join([f"\n   :assumption ({symbol} {expr})" for symbol,expr in self.assumption.items()])
        fairness_str = "".join([f"\n   :fairness ({symbol} {expr})" for symbol,expr in self.fairness.items()])
        reachable_str = "".join([f"\n   :reachable ({symbol} {expr})" for symbol,expr in self.reachable.items()])
        current_str = "".join([f"\n   :current ({symbol} {expr})" for symbol,expr in self.current.items()])
        query_str = "".join([f"\n   :query ({symbol} ({' '.join(labels)}))" for symbol,labels in self.query.items()])

        queries_str = ""
        for query in self.queries:
            query_list_str = " ".join([f"({symbol} ({' '.join(labels)}))" for symbol,labels in query.items()])
            queries_str += f"\n   :queries ({query_list_str})"

        s =  f"(check-system {self.symbol} "
        s += f"\n   :input ({input_str}) "
        s += f"\n   :output ({output_str}) "
        s += f"\n   :local ({local_str}) "
        if assumption_str:
            s += assumption_str
        if fairness_str:
            s += fairness_str
        if reachable_str:
            s += reachable_str
        if current_str:
            s += current_str
        if query_str:
            s += query_str
        if queries_str:
            s += queries_str

        return s + ")"

    def to_json(self) -> dict:
        return { 
            "command": "check-system",
            "symbol": self.symbol,
            "input": [to_json_sorted_var(symbol,sort) for symbol,sort in self.input],
            "output": [to_json_sorted_var(symbol,sort) for symbol,sort in self.output], 
            "local": [to_json_sorted_var(symbol,sort) for symbol,sort in self.local], 
            "assumption": [{"symbol": s, "formula": a.to_json()} for s,a in self.assumption.items()], 
            "fairness": [{"symbol": s, "formula": f.to_json()} for s,f in self.fairness.items()], 
            "reachable": [{"symbol": s, "formula": r.to_json()} for s,r in self.reachable.items()], 
            "current": [{"symbol": s, "formula": c.to_json()} for s,c in self.current.items()], 
            "query": [{"symbol": s, "formulas": q} for s,q in self.query.items()],
            "queries": [[{"symbol": s, "formulas": q} for s,q in query.items()] for query in self.queries]
        }


class MCILProgram():

    def __init__(self, commands: list[MCILCommand]):
        self.commands: list[MCILCommand] = commands

    def get_exprs(self) -> list[MCILExpr]:
        return [e for cmd in self.commands for e in cmd.get_exprs()]

    def get_check_system_cmds(self) -> list[MCILCheckSystem]:
        return [cmd for cmd in self.commands if isinstance(cmd, MCILCheckSystem)]

    def __str__(self) -> str:
        return "\n".join(str(cmd) for cmd in self.commands)

    def to_json(self) -> list:
        return [cmd.to_json() for cmd in self.commands]


class MCILExit(MCILCommand):
    pass


MCIL_BOOL_CONST = lambda x: MCILConstant(MCIL_BOOL_SORT, x)
MCIL_BITVEC_CONST = lambda x,y: MCILConstant(MCIL_BITVEC_SORT(x), y)
MCIL_ARRAY_CONST = lambda x,y,z: MCILApply(MCIL_ARRAY_SORT(x,y), MCILIdentifier("const", []), [z])
MCIL_INT_CONST = lambda x: MCILConstant(MCIL_INT_SORT, x)
MCIL_ENUM_CONST = lambda x,y: MCILConstant(MCIL_ENUM_SORT(x), y)

MCIL_EQ_EXPR = lambda x,y: MCILApply(MCIL_BOOL_SORT, MCILIdentifier("=", []), [x,y])
MCIL_AND_EXPR = lambda x,y: MCILApply(MCIL_BOOL_SORT, MCILIdentifier("and", []), [x,y])
MCIL_OR_EXPR = lambda x,y: MCILApply(MCIL_BOOL_SORT, MCILIdentifier("or", []), [x,y])

MCIL_INT_NEG_EXPR = lambda x: MCILApply(MCIL_INT_SORT, MCILIdentifier("-", []), [x])

MCIL_SELECT_EXPR = lambda x,y: MCILApply(MCIL_NO_SORT, MCILIdentifier("select", []), [x,y])
MCIL_STORE_EXPR = lambda x,y,z: MCILApply(MCIL_NO_SORT, MCILIdentifier("store", []), [x,y,z])

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
    ("true", 0):       lambda _: ([], MCIL_BOOL_SORT),
    ("false", 0):      lambda _: ([], MCIL_BOOL_SORT),
    ("not", 0):        lambda _: ([MCIL_BOOL_SORT], MCIL_BOOL_SORT),
    ("=>", 0):         lambda _: ([MCIL_BOOL_SORT, MCIL_BOOL_SORT], MCIL_BOOL_SORT),
    ("and", 0):        lambda A: ([MCIL_BOOL_SORT for _ in range(0,A)], MCIL_BOOL_SORT),
    ("or", 0):         lambda A: ([MCIL_BOOL_SORT for _ in range(0,A)], MCIL_BOOL_SORT),
    ("xor", 0):        lambda A: ([MCIL_BOOL_SORT for _ in range(0,A)], MCIL_BOOL_SORT),
    ("=", 0):          lambda A: ([A[0] for _ in range(0,A[1])], MCIL_BOOL_SORT),
    ("distinct", 0):   lambda A: ([A[0] for _ in range(0,A[1])], MCIL_BOOL_SORT),
    ("ite", 0):        lambda A: ([MCIL_BOOL_SORT, A, A], A),
    ("const", 0):      lambda A: ([MCIL_ANY_SORT], A),
    ("OnlyChange", 0): lambda A: ([MCIL_ANY_SORT for _ in range(0,A)], MCIL_BOOL_SORT),
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

INT_RANK_TABLE: RankTable = {
    ("-", 0):         lambda A: ([MCIL_INT_SORT for _ in range(0,A)], MCIL_INT_SORT),
    ("+", 0):         lambda _: ([MCIL_INT_SORT, MCIL_INT_SORT], MCIL_INT_SORT),
    ("*", 0):         lambda _: ([MCIL_INT_SORT, MCIL_INT_SORT], MCIL_INT_SORT),
    ("/", 0):         lambda _: ([MCIL_INT_SORT, MCIL_INT_SORT], MCIL_INT_SORT),
    ("div", 0):       lambda _: ([MCIL_INT_SORT, MCIL_INT_SORT], MCIL_INT_SORT),
    ("mod", 0):       lambda _: ([MCIL_INT_SORT, MCIL_INT_SORT], MCIL_INT_SORT),
    ("abs", 0):       lambda _: ([MCIL_INT_SORT], MCIL_INT_SORT),
    ("<=", 0):        lambda A: ([MCIL_INT_SORT for _ in range(0,A)], MCIL_BOOL_SORT),
    ("<", 0):         lambda A: ([MCIL_INT_SORT for _ in range(0,A)], MCIL_BOOL_SORT),
    (">=", 0):        lambda A: ([MCIL_INT_SORT for _ in range(0,A)], MCIL_BOOL_SORT),
    (">", 0):         lambda A: ([MCIL_INT_SORT for _ in range(0,A)], MCIL_BOOL_SORT),
    ("divisible", 1): lambda _: ([MCIL_INT_SORT], MCIL_BOOL_SORT),
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
    elif identifier.check({"=", "distinct"}, 0):
        # (par (A) (= A ... A Bool))
        # (par (A) (distinct A ... A Bool))
        if len(node.children) < 1:
            return False

        param = node.children[0].sort
        rank = CORE_RANK_TABLE[(identifier.symbol, 0)]((param, len(node.children)))

        return sort_check_apply_rank(node, rank)
    elif identifier.check({"ite"}, 0):
        # (par (A) (ite Bool A A A))
        if len(node.children) < 3:
            return False

        param = node.children[2].sort
        rank = CORE_RANK_TABLE[identifier_class](param)

        return sort_check_apply_rank(node, rank)
    elif identifier.check({"and", "or", "xor"}, 0):
        # (and Bool ... Bool Bool)
        # (or Bool ... Bool Bool)
        # (xor Bool ... Bool Bool)
        if len(node.children) < 2:
            return False

        param = len(node.children)
        rank = CORE_RANK_TABLE[identifier_class](param)

        return sort_check_apply_rank(node, rank)
    elif identifier.check({"const"}, 0):
        if len(node.children) < 1:
            return False

        if not isinstance(node.children[0], MCILConstant):
            return False

        rank = CORE_RANK_TABLE[identifier_class](node.sort)

        return sort_check_apply_rank(node, rank)
    elif identifier.check({"OnlyChange"}, 0):
        if len(node.children) < 1:
            return False

        if any([not isinstance(c, MCILVar) for c in node.children]):
            return False

        param = len(node.children)
        rank = CORE_RANK_TABLE[identifier_class](param)

        return sort_check_apply_rank(node, rank)

    rank = CORE_RANK_TABLE[identifier_class](None)
    return sort_check_apply_rank(node, rank)


def sort_check_apply_bitvec(node: MCILApply) -> bool:
    """Returns true if 'node' corresponds to a valid rank in SMT-LIB2 FixedSizeBitVectors Theory. Assumes that node's identifier is in BITVEC_RANK_TABLE."""
    identifier = node.identifier
    identifier_class = identifier.get_class()

    if identifier_class not in BITVEC_RANK_TABLE:
        return False
    elif identifier.check({"concat"}, 0):
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
    elif identifier.check({"extract"}, 2):
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
    elif identifier.check({"zero_extend", "sign_extend"}, 1):
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
    elif identifier.check({"rotate_left", "rotate_right"}, 1):
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


def sort_check_apply_int(node: MCILApply) -> bool:
    # "-", "+", "*", "/", "div", "mod", "abs", ">=", ">", "<=", "<", "divisible"
    identifier = node.identifier
    identifier_class = identifier.get_class()

    if identifier_class not in INT_RANK_TABLE:
        return False
    elif identifier.check({"-"}, 0):
        # (- Int Int Int)
        # (- Int Int)
        if len(node.children) < 1 or len(node.children) > 2:
            return False

        param = len(node.children)
        rank = INT_RANK_TABLE[identifier_class](param)

        return sort_check_apply_rank(node, rank)
    elif identifier.check({">=", ">", "<=", "<"}, 0):
        # (- Int Int Int)
        # (- Int Int)
        if len(node.children) < 2 or len(node.children) > 3:
            return False

        param = len(node.children)
        rank = INT_RANK_TABLE[identifier_class](param)

        return sort_check_apply_rank(node, rank)

    rank = INT_RANK_TABLE[identifier_class](None)
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


def sort_check_apply_qf_lia(node: MCILApply) -> bool:
    identifier_class = (node.identifier.symbol, node.identifier.num_indices())

    # remove some unsupported functions from theory of Ints
    lia_rank_table = copy(INT_RANK_TABLE)
    del lia_rank_table[("/", 0)]
    del lia_rank_table[("div", 0)]
    del lia_rank_table[("mod", 0)]
    del lia_rank_table[("abs", 0)]

    if identifier_class in CORE_RANK_TABLE:
        return sort_check_apply_core(node)
    elif identifier_class in lia_rank_table:
        status = sort_check_apply_int(node)

        if not status:
            return status

        # Special case for LIA (from SMT-LIB): 
        # Terms containing * with _concrete_ coefficients are also allowed, that
        # is, terms of the form c, (* c x), or (* x c)  where x is a free constant
        # and c is a term of the form n or (- n) for some numeral n.
        if node.identifier.check({"*"}, 0):
            lhs,rhs = node.children
            if isinstance(lhs, MCILApply):
                if not lhs.identifier.check({"-"}, 0):
                    return False
                elif not len(lhs.children) == 1:
                    return False
                elif not isinstance(lhs.children[0], MCILConstant):
                    return False
                elif not isinstance(rhs, MCILVar):
                    return False
            elif isinstance(rhs, MCILApply):
                if not rhs.identifier.check({"-"}, 0):
                    return False
                elif not len(rhs.children) == 1:
                    return False
                elif not isinstance(rhs.children[0], MCILConstant):
                    return False
                elif not isinstance(lhs, MCILVar):
                    return False

        return status

    return False


def sort_check_apply_qf_nia(node: MCILApply) -> bool:
    identifier_class = (node.identifier.symbol, node.identifier.num_indices())

    if identifier_class in CORE_RANK_TABLE:
        return sort_check_apply_core(node)
    elif identifier_class in INT_RANK_TABLE:
        return sort_check_apply_int(node)

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


NO_LOGIC = MCILLogic("Not Set", 
                    {("Bool", 0)}, 
                    set(CORE_RANK_TABLE.keys()), 
                    sort_check_apply_core)

QF_BV = MCILLogic("QF_BV", 
                {("Bool", 0), ("BitVec", 1)}, 
                CORE_RANK_TABLE.keys() | BITVEC_RANK_TABLE.keys(), 
                sort_check_apply_qf_bv)

QF_ABV = MCILLogic("QF_ABV", 
                {("Bool", 0), ("BitVec", 1), ("Array", 0)}, 
                CORE_RANK_TABLE.keys() | BITVEC_RANK_TABLE.keys() | ARRAY_RANK_TABLE.keys(), 
                sort_check_apply_qf_abv)

QF_LIA = MCILLogic("QF_LIA", 
                {("Bool", 0), ("Int", 0)}, 
                CORE_RANK_TABLE.keys() | INT_RANK_TABLE.keys(), 
                sort_check_apply_qf_lia)

QF_NIA = MCILLogic("QF_NIA", 
                {("Bool", 0), ("Int", 0)}, 
                CORE_RANK_TABLE.keys() | INT_RANK_TABLE.keys(), 
                sort_check_apply_qf_nia)

LOGIC_TABLE: dict[str, MCILLogic] = {
    "QF_BV": QF_BV,
    "QF_ABV": QF_ABV,
    "QF_LIA": QF_LIA,
    "QF_NIA": QF_NIA
}

class MCILSystemContext():

    def __init__(self):
        self._system_stack: list[tuple[str, MCILSystemCommand]] = []

    def push(self, new: tuple[str, MCILSystemCommand]):
        self._system_stack.append(new)

    def pop(self) -> tuple[str, MCILSystemCommand]:
        return self._system_stack.pop()

    def copy(self) -> MCILSystemContext:
        new_system_stack = self._system_stack.copy()
        new = MCILSystemContext()
        for s in new_system_stack:
            new.push(s)
        return new

    def get_top(self) -> Optional[tuple[str, MCILSystemCommand]]:
        """Returns the system at the top of the stack."""
        if len(self._system_stack) == 0:
            return None
        return self._system_stack[-1]

    def get_bottom(self) -> Optional[tuple[str, MCILSystemCommand]]:
        """Returns the system at the bottom of the stack (top-level system)."""
        if len(self._system_stack) == 0:
            return None
        return self._system_stack[0]

    def get_subsystems(self) -> list[tuple[str, MCILSystemCommand]]:
        if len(self._system_stack) < 3:
            return []
        return self._system_stack[2:]

    def get_input_symbols(self) -> set[str]:
        top = self.get_top()
        if not top:
            raise KeyError("No system in context")
        (_,system) = top
        return system.input_symbols

    def get_output_symbols(self) -> set[str]:
        top = self.get_top()
        if not top:
            raise KeyError("No system in context")
        (_,system) = top
        return system.output_symbols
    
    def get_local_symbols(self) -> set[str]:
        top = self.get_top()
        if not top:
            raise KeyError("No system in context")
        (_,system) = top
        return system.local_symbols

    def get_sort(self, symbol: str) -> MCILSort:
        top = self.get_top()
        if not top:
            raise KeyError("No system in context")
        (_,system) = top
        sort = system.get_sort(symbol)
        if not sort:
            raise KeyError(symbol)
        return sort

    def get_scope_symbols(self) -> list[str]:
        if len(self._system_stack) < 2:
            return []
        top_level = self._system_stack[1]
        top_level_symbol,_ = top_level
        return [top_level_symbol] + [name for name,_ in self.get_subsystems()]

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

    def __str__(self) -> str:
        return f"[{', '.join([f'({sym}, {sys.symbol})' for sym,sys in self._system_stack])}]"

# A RenameMap maps variables in a system context to another variable and system context. This is used for mapping
# input/output variables of subsystem. The mapped-to variable/system context pair may also be in the rename map, in
# which case another lookup is necessary.
RenameMap = dict[tuple[str, MCILSystemContext], tuple[str, MCILSystemContext]]

def get_scoped_var_symbol(var_symbol: str, system_context: MCILSystemContext) -> str:
    return "::".join(system_context.get_scope_symbols() + [var_symbol])


class MCILContext():

    def __init__(self):

        self.declared_sorts: dict[MCILIdentifier, int] = {}
        self.declared_enum_sorts: dict[str, list[str]] = {}
        self.defined_sorts: set[MCILSort] = set()
        self.sorts: dict[str, MCILSort] = {}
        self.sort_symbols: set[str] = set()

        self.declared_functions: dict[str, Rank] = {}
        self.defined_functions: dict[str, tuple[Rank, MCILExpr]] = {}
        self.defined_function_input_vars: dict[str, list[MCILVar] ] = {}

        self.declared_consts: dict[str, MCILSort] = {}

        self.defined_systems: dict[str, MCILDefineSystem] = {}
        self.system_context = MCILSystemContext()
        self.cur_check_system: Optional[MCILCheckSystem] = None
        self.rename_map: RenameMap = {}

        self.input_vars: set[str] = set()
        self.output_vars: set[str] = set()
        self.local_vars: set[str] = set()
        self.var_sorts: dict[str, MCILSort] = {}

        self.bound_let_vars: dict[str, MCILExpr] = {}

        self.cur_command: Optional[MCILCommand] = None

        self.const_arrays: set[tuple[MCILSort, MCILConstant, MCILExpr]] = set()

        self.symbols: set[str] = set()

        self.set_logic(NO_LOGIC)

    def set_logic(self, logic: MCILLogic) -> None:
        # remove symbols from previous logic
        for symbol,_ in logic.function_symbols | logic.sort_symbols:
            self.sort_symbols.discard(symbol)
            self.symbols.discard(symbol)

        # TODO: Check for conflicts between symbols and logic symbols

        self.logic = logic
        self.symbols.update([symbol for symbol,_ in logic.sort_symbols])
        self.sort_symbols.update([symbol for symbol,_ in logic.sort_symbols])
        self.symbols.update([symbol for symbol,_ in logic.function_symbols])

    def add_declared_sort(self, ident: MCILIdentifier, arity: int) -> None:
        self.declared_sorts[ident] = arity
        self.symbols.add(ident.symbol)
        self.sorts[ident.symbol] = MCILSort(ident, [])

    def add_declared_enum_sort(self, symbol: str, vals: list[str]) -> None:
        self.declared_enum_sorts[symbol] = vals
        self.defined_sorts.add(MCIL_ENUM_SORT(symbol))
        self.sort_symbols.add(symbol)
        self.symbols.add(symbol)
        [self.symbols.add(v) for v in vals]

    def add_defined_sort(self, sort: MCILSort) -> None:
        self.defined_sorts.add(sort)
        self.sort_symbols.add(sort.symbol)
        self.symbols.add(sort.symbol)

    def add_declared_function(self, symbol: str, rank: Rank) -> None:
        self.declared_functions[symbol] = rank
        self.symbols.add(symbol)

    def add_defined_function(self, define_fun: MCILDefineFun) -> None:
        symbol = define_fun.symbol

        input_sorts = [sort for _,sort in define_fun.input]
        signature = (Rank((input_sorts, define_fun.output_sort)), define_fun.body)
        input_vars = [MCILVar(sort, sym, False) for sym,sort in define_fun.input]

        self.defined_functions[symbol] = signature
        self.defined_function_input_vars[symbol] = input_vars
        self.symbols.add(symbol)

    def add_declared_const(self, symbol: str, sort: MCILSort) -> None:
        self.declared_consts[symbol] = sort
        self.symbols.add(symbol)

    def add_defined_system(self, symbol: str, system: MCILDefineSystem) -> None:
        self.defined_systems[symbol] = system
        self.symbols.add(symbol)

    def add_bound_let_var(self, symbol: str, expr: MCILExpr) -> None:
        self.bound_let_vars[symbol] = expr
        self.symbols.add(symbol)

    def remove_bound_let_var(self, symbol: str) -> None:
        if symbol in self.bound_let_vars:
            del self.bound_let_vars[symbol]
            self.symbols.remove(symbol)

    def add_vars(self, vars: list[tuple[str, MCILSort]]) -> None:
        self.var_sorts.update({symbol:sort for symbol,sort in vars})
        self.symbols.update([symbol for symbol,_ in vars])

    def remove_vars(self, vars: list[tuple[str, MCILSort]]) -> None:
        for symbol,_ in vars:
            del self.var_sorts[symbol]
            self.symbols.discard(symbol)

    def set_system_vars(
        self, 
        input: list[tuple[str, MCILSort]],
        output: list[tuple[str, MCILSort]],
        local: list[tuple[str, MCILSort]]
    ) -> None:
        self.input_vars = set([symbol for symbol,_ in input])
        self.output_vars = set([symbol for symbol,_ in output])
        self.local_vars = set([symbol for symbol,_ in local])

        self.add_vars(input + output + local)

    def push_system(
        self, 
        symbol: str, 
        new_system: MCILSystemCommand,
        params: list[str]
    ) -> None:
        # print(f"Pushing: {symbol} ({type(new_system).__name__})")

        # Remove symbols from current top of system stack and maintain rename_map
        top = self.system_context.get_top()
        if top:
            (_,cur_system) = top
            self.remove_vars(cur_system.input + cur_system.output + cur_system.local)
            self.update_rename_map(params, new_system, symbol)

        self.set_system_vars(
            new_system.input, new_system.output, new_system.local
        )

        self.system_context.push((symbol, new_system))

    def pop_system(self) -> tuple[str, MCILSystemCommand]:
        old_symbol,old_system = self.system_context.pop()

        # Remove symbols from current top of system stack and maintain rename_map
        self.remove_vars(old_system.input + old_system.output + old_system.local)

        top = self.system_context.get_top()
        if top:
            (cs,cur_system) = top
            self.set_system_vars(cur_system.input, cur_system.output, cur_system.local)
            # print(f"Popping: {old_symbol} (Current: {cs})")
        elif self.cur_check_system:
            # print(f"Popping: {old_symbol}")
            pass

        return (old_symbol, old_system)

    def lookup_var(self, symbol: str, system_context: MCILSystemContext) -> tuple[str, MCILSystemContext]:
        """Returns the variable symbol and system context that `symbol`/`system_context` point to via `rename_map`."""
        cur_var, cur_system_context = symbol, system_context
        while (cur_var, cur_system_context) in self.rename_map:
            (cur_var, cur_system_context) = self.rename_map[(cur_var, cur_system_context)]
        return (cur_var, cur_system_context)

    def update_rename_map(
        self, 
        signature: list[str],
        target_system: MCILSystemCommand,
        target_system_symbol: str,
    ) -> None:
        target_context = self.system_context.copy() # need to copy (only copies pointers)
        target_context.push((target_system_symbol, target_system))

        top = self.system_context.get_top()
        if not top:
            return

        (cur_symbol, cur_system) = top

        # If we are mapping check-system to define-system variables,
        # then we need to map each input, output, and local.
        # If we are mapping define-system to define-system variables,
        # then we only need to map each input and output.
        if isinstance(cur_system, MCILCheckSystem):
            target_signature = target_system.get_full_signature()
        else:
            target_signature = target_system.get_signature()

        # print(f"Mapping:")
        # print(f"{''.join([f'{s:13}' for s in signature])}")
        # print(f"{''.join([f'{s:13}' for s in target_signature])}")

        for cmd_var,target_var in zip(signature, target_signature):
            self.rename_map[(target_var, target_context)] = (cmd_var, self.system_context.copy())


def postorder_mcil(expr: MCILExpr, context: MCILContext):
    """Perform an iterative postorder traversal of `expr`, maintaining `context`."""
    stack: list[tuple[bool, MCILExpr]] = []
    stack.append((False, expr))

    while len(stack) > 0:
        (seen, cur) = stack.pop()

        if seen and isinstance(cur, MCILLetExpr):
            for (v,e) in cur.get_binders():
                context.remove_bound_let_var(v)
            yield cur
        elif seen and isinstance(cur, MCILBind):
            for (v,e) in cur.get_binders():
                context.add_bound_let_var(v,e)
        elif seen:
            yield cur
        else:
            stack.append((True, cur))
            for child in cur.children:
                stack.append((False, child))


def sort_check(program: MCILProgram) -> tuple[bool, MCILContext]:
    context: MCILContext = MCILContext()
    status: bool = True

    def sort_check_expr(node: MCILExpr, context: MCILContext, no_prime: bool, is_init_expr: bool) -> bool:
        """Return true if node is well-sorted where `no_prime` is true if primed variables are disabled and `prime_input` is true if input variable are allowed to be primed (true for check-system assumptions and reachability conditions)."""
        status = True

        for expr in postorder_mcil(node, context):
            if isinstance(expr, MCILConstant):
                if expr.sort.symbol not in context.sort_symbols:
                    logger.error(f"Error: sort unrecognized '{expr.sort}' ({expr}).\n\tCurrent logic: {context.logic.symbol}")
                    status = False
            elif isinstance(expr, MCILVar) and expr.symbol in context.input_vars:
                expr.sort = context.var_sorts[expr.symbol]

                if expr.sort.symbol not in context.sort_symbols:
                    logger.error(f"Error: sort unrecognized '{expr.sort}' ({expr}).\n\tCurrent logic: {context.logic.symbol}")
                    status = False

                if expr.prime and no_prime:
                    logger.error(f"Error: primed variables only allowed in system transition or invariant relation ({expr.symbol}).\n\t{context.cur_command}")
                    status = False
            elif isinstance(expr, MCILVar) and expr.symbol in context.output_vars:
                expr.sort = context.var_sorts[expr.symbol]
                
                if expr.sort.symbol not in context.sort_symbols:
                    logger.error(f"Error: sort unrecognized '{expr.sort}' ({expr}).\n\tCurrent logic: {context.logic.symbol}")
                    status = False

                if expr.prime and no_prime:
                    logger.error(f"Error: primed variables only allowed in system transition or invariant relation ({expr.symbol}).\n\t{context.cur_command}")
                    status = False
            elif isinstance(expr, MCILVar) and expr.symbol in context.local_vars:
                expr.sort = context.var_sorts[expr.symbol]

                if expr.sort.symbol not in context.sort_symbols:
                    logger.error(f"Error: sort unrecognized '{expr.sort}' ({expr}).\n\tCurrent logic: {context.logic.symbol}")
                    status = False

                if expr.prime and no_prime:
                    logger.error(f"Error: primed variables only allowed in system transition or invariant relation ({expr.symbol}).\n\t{context.cur_command}")
                    status = False
            elif isinstance(expr, MCILVar) and expr.symbol in context.bound_let_vars:
                if expr.prime:
                    logger.error(f"Error: bound variables cannot be primed ({expr})")
                    status = False
                
                expr.sort = context.bound_let_vars[expr.symbol].sort
            elif isinstance(expr, MCILVar) and expr.symbol in context.var_sorts:
                if expr.prime:
                    logger.error(f"Error: only system variables be primed ({expr})")
                    status = False

                expr.sort = context.var_sorts[expr.symbol]

                if expr.sort.symbol not in context.sort_symbols:
                    logger.error(f"Error: sort unrecognized '{expr.sort}' ({expr}).\n\tCurrent logic: {context.logic.symbol}")
                    status = False
            elif isinstance(expr, MCILVar) and expr.symbol in context.declared_consts:
                if expr.prime:
                    logger.error(f"Error: consts cannot be primed ({expr})")
                    status = False

                expr.sort = context.declared_consts[expr.symbol]
            elif isinstance(expr, MCILVar) and expr.symbol in context.defined_functions:
                if expr.prime:
                    logger.error(f"Error: consts cannot be primed ({expr})")
                    status = False

                # constants defined using define-fun 
                ((inputs, output), _) = context.defined_functions[expr.symbol]

                if len(inputs) != 0:
                    logger.error(f"Error: function signature does not match definition.\n\t{expr}\n\t{expr.symbol}")
                    status = False

                expr.sort = output
            elif isinstance(expr, MCILVar):
                logger.error(f"Error: symbol '{expr.symbol}' not declared.\n\t{context.cur_command}")
                status = False
            elif isinstance(expr, MCILApply):
                if expr.identifier.get_class() in context.logic.function_symbols:
                    if not context.logic.sort_check(expr):
                        logger.error(f"Error: function signature does not match definition.\n\t{expr}\n\t{expr.identifier} {[str(a.sort) for a in expr.children]}")
                        status = False
                elif expr.identifier.symbol in context.defined_functions:
                    (rank, _) = context.defined_functions[expr.identifier.symbol]

                    if not sort_check_apply_rank(expr, rank):
                        logger.error(f"Error: function call does not match definition.\n\t{expr}\n\t{expr.identifier} {[str(a.sort) for a in expr.children]}")
                        status = False
                else:
                    logger.error(f"Error: symbol '{expr.identifier.symbol}' not recognized ({expr}).\n\t{context.cur_command}")
                    status = False

                # constant arrays must be handled separately, maintain a list of
                # them
                if is_const_array_expr(expr):
                    # this is a safe cast since expr is well-sorted, see sort check
                    # of "const" in sort_check_apply_core
                    const_expr = cast(MCILConstant, expr.children[0])
                    context.const_arrays.add((expr.sort, const_expr, expr))

            elif isinstance(expr, MCILLetExpr):
                # TODO: check for variable name clashes
                expr.sort = expr.get_expr().sort
            else:
                logger.error(f"Error: expr type '{expr.__class__}' not recognized ({expr}).\n\t{context.cur_command}")
                status = False

        return status
    # end sort_check_expr

    for cmd in program.commands:
        context.cur_command = cmd

        if isinstance(cmd, MCILSetLogic):
            if cmd.logic not in LOGIC_TABLE:
                logger.error(f"Error: logic {cmd.logic} unsupported.")
                status = False
            else:
                context.set_logic(LOGIC_TABLE[cmd.logic])
        elif isinstance(cmd, MCILDeclareSort):
            # TODO: move this warning to mcil2btor.py
            logger.error(f"Warning: declare-sort command unsupported, ignoring.")
        elif isinstance(cmd, MCILDefineSort):
            if cmd.symbol in context.symbols:
                logger.error(f"Error: symbol '{cmd.symbol}' already in use.\n\t{cmd}")
                status = False

            # TODO
            context.add_defined_sort(cmd.definition)
        elif isinstance(cmd, MCILDeclareEnumSort):
            if cmd.symbol in context.symbols:
                logger.error(f"Error: symbol '{cmd.symbol}' already in use.\n\t{cmd}")
                status = False

            context.add_declared_enum_sort(cmd.symbol, cmd.values)
        elif isinstance(cmd, MCILDeclareConst):
            if cmd.symbol in context.symbols:
                logger.error(f"Error: symbol '{cmd.symbol}' already in use.\n\t{cmd}")
                status = False

            context.add_declared_const(cmd.symbol, cmd.sort)
        elif isinstance(cmd, MCILDeclareFun):
            if cmd.symbol in context.symbols:
                logger.error(f"Error: symbol '{cmd.symbol}' already in use.\n\t{cmd}")
                status = False

            context.add_declared_function(cmd.symbol, Rank((cmd.inputs, cmd.output_sort)))
        elif isinstance(cmd, MCILDefineFun):
            if cmd.symbol in context.symbols:
                logger.error(f"Error: symbol '{cmd.symbol}' already in use.\n\t{cmd}")
                status = False

            context.add_vars(cmd.input)

            status = status and sort_check_expr(cmd.body, context, no_prime=True, is_init_expr=False)

            context.remove_vars(cmd.input)

            context.add_defined_function(cmd)
        elif isinstance(cmd, MCILDefineSystem):
            # TODO: check for variable name clashes across cmd.input, cmd.output, cmd.local
            # TODO: check for valid sort symbols
            context.push_system(cmd.symbol, cmd, [])
            # context.add_system_vars(cmd.input, cmd.output, cmd.local)

            status = status and sort_check_expr(cmd.init, context, no_prime=True, is_init_expr=True)
            status = status and sort_check_expr(cmd.trans, context, no_prime=False, is_init_expr=False)
            status = status and sort_check_expr(cmd.inv, context, no_prime=False, is_init_expr=False)

            for name,subsystem in cmd.subsystem_signatures.items():
                # TODO: check for cycles in system dependency graph
                (sys_symbol, signature_symbols) = subsystem

                if sys_symbol not in context.defined_systems:
                    logger.error(f"Error: system '{sys_symbol}' not defined in context.\n\t{cmd}")
                    status = False
                    return (False, context)

                # check that each symbol in signature is in the context
                signature: list[tuple[str, MCILSort]] = []
                for symbol in signature_symbols:
                    if symbol not in context.var_sorts:
                        logger.error(f"Error: variable '{symbol}' not declared.\n\t{cmd}")
                        status = False
                        signature.append(("", MCIL_NO_SORT))
                        continue

                    signature.append((symbol, context.var_sorts[symbol]))

                target_system = context.defined_systems[sys_symbol]
                target_signature = target_system.input + target_system.output

                if len(signature) != len(target_signature):
                    logger.error(f"Error: subsystem signature does not match target system ({sys_symbol}).\n\t{context.defined_systems[sys_symbol].input + context.defined_systems[sys_symbol].output}\n\t{signature}")
                    status = False
                    continue

                for (_,cmd_sort),(_,target_sort) in zip(signature, target_signature):
                    if cmd_sort != target_sort:
                        logger.error(f"Error: subsystem signature does not match target system ({sys_symbol}).\n\t{context.defined_systems[sys_symbol].input + context.defined_systems[sys_symbol].output}\n\t{signature}")
                        status = False
                        continue

                cmd.subsystems[name] = context.defined_systems[sys_symbol]

            context.defined_systems[cmd.symbol] = cmd
            cmd.var_sorts.update({
                symbol:sort for symbol,sort in cmd.input + cmd.output + cmd.local
            })
            
            context.pop_system()
        elif isinstance(cmd, MCILCheckSystem):
            if not cmd.symbol in context.defined_systems:
                logger.error(f"Error: system '{cmd.symbol}' undefined.\n\t{cmd}")
                status = False
                continue

            context.push_system(cmd.symbol, cmd, [])
            system = context.defined_systems[cmd.symbol]

            if len(system.input) != len(cmd.input):
                logger.error(f"Error: input variables do not match target system ({system.symbol})."
                    f"\n\t{', '.join([f'({v}: {s})' for v,s in system.input])}"
                    f"\n\t{', '.join([f'({v}: {s})' for v,s in cmd.input])}")
                status = False
                continue

            for (_,sort1),(_,sort2) in zip(system.input, cmd.input):
                if sort1 != sort2:
                    logger.error(f"Error: sorts do not match in check-system (expected {sort1}, got {sort2})")
                    status = False
                else:
                    pass
                    # i2.var_type = MCILVarType.INPUT
                # cmd.rename_map[v1] = v2

            if len(system.output) != len(cmd.output):
                logger.error(f"Error: output variables do not match target system ({system.symbol})."
                    f"\n\t{', '.join([f'({v}: {s})' for v,s in system.output])}"
                    f"\n\t{', '.join([f'({v}: {s})' for v,s in cmd.output])}")
                status = False
                continue

            for (_,sort1),(_,sort2) in zip(system.output, cmd.output):
                if sort1 != sort2:
                    logger.error(f"Error: sorts do not match in check-system (expected {sort1}, got {sort2})")
                    status = False
                else:
                    pass
                # cmd.rename_map[v1] = v2

            if len(system.local) != len(cmd.local):
                logger.error(f"Error: local variables do not match target system ({system.symbol})."
                    f"\n\t{', '.join([f'({v}: {s})' for v,s in system.local])}"
                    f"\n\t{', '.join([f'({v}: {s})' for v,s in cmd.local])}")
                status = False
                continue

            for (_,sort1),(_,sort2) in zip(system.local, cmd.local):
                if sort1 != sort2:
                    logger.error(f"Error: sorts do not match in check-system (expected {sort1}, got {sort2})")
                    status = False
                else:
                    pass
                # cmd.rename_map[v1] = v2

            for expr in cmd.assumption.values():
                status = status and sort_check_expr(expr, context, False, is_init_expr=False)

            for expr in cmd.reachable.values():
                status = status and sort_check_expr(expr, context, False, is_init_expr=False)

            for expr in cmd.fairness.values():
                status = status and sort_check_expr(expr, context, False, is_init_expr=False)

            for expr in cmd.current.values():
                status = status and sort_check_expr(expr, context, False, is_init_expr=False)

            cmd.var_sorts.update({
                symbol:sort for symbol,sort in cmd.input + cmd.output + cmd.local
            })

            context.pop_system()
        elif isinstance(cmd, MCILExit):
            return (status, context)
        else:
            raise NotImplementedError

    return (status, context)


def inline_funs(program: MCILProgram, context: MCILContext) -> None:
    """Perform function inlining on each expression in `program`."""
    for top_expr in program.get_exprs():
        for expr in postorder_mcil(top_expr, context):
            if (
                isinstance(expr, MCILApply) 
                and expr.identifier.symbol in context.defined_functions
            ):
                fun_symbol = expr.identifier.symbol

                _,fun_def = context.defined_functions[fun_symbol]
                fun_def_input_vars = context.defined_function_input_vars[fun_symbol]
                
                var_map = {arg:val for arg,val in zip(fun_def_input_vars, expr.children)}
                
                expr.replace(rename_vars(fun_def, var_map, context))


def to_binary_applys(program: MCILProgram, context: MCILContext) -> None:
    """Replace all multi-arity functions (=, and, or, <, etc.) to binary versions."""
    for top_expr in program.get_exprs():
        for expr in postorder_mcil(top_expr, context):
            if (
                isinstance(expr, MCILApply) 
                and expr.identifier.check({"and", "or", "xor", "=", "distinct"}, 0)
                and len(expr.children) > 2
            ):
                new_expr = MCILApply(expr.sort, expr.identifier, [expr.children[-2], expr.children[-1]])
                for i in range(3, len(expr.children)+1):
                    new_expr = MCILApply(expr.sort, expr.identifier, [expr.children[-i], new_expr])

                expr.replace(new_expr)
            elif (
                isinstance(expr, MCILApply) 
                and expr.identifier.check({"<=", "<", ">=", ">"}, 0) 
                and len(expr.children) == 3
            ):
                new_expr = MCILApply(expr.sort, expr.identifier, 
                    [
                        expr.children[0],
                        MCILApply(expr.sort, expr.identifier,
                            [
                                expr.children[1],
                                expr.children[2]
                            ]
                        )
                    ]
                )

                expr.replace(new_expr)


def to_qfbv(program: MCILProgram, int_width: int):

    SORT_MAP: dict[MCILSort, MCILSort] = {
        MCIL_INT_SORT: MCIL_BITVEC_SORT(int_width)
    }

    UNARY_OPERATOR_MAP = {
        "-": MCILIdentifier("bvneg", []),
    }

    BINARY_OPERATOR_MAP = {
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
        if isinstance(expr, MCILApply):
            if len(expr.children) == 1 and expr.identifier.symbol in UNARY_OPERATOR_MAP:
                expr.identifier = UNARY_OPERATOR_MAP[expr.identifier.symbol]
            elif len(expr.children) == 2 and expr.identifier.symbol in BINARY_OPERATOR_MAP:
                expr.identifier = BINARY_OPERATOR_MAP[expr.identifier.symbol]
            
        if expr.sort in SORT_MAP:
            expr.sort = SORT_MAP[expr.sort]

    for command in program.commands:
        if isinstance(command, MCILSetLogic):
            command.logic = "QF_BV"
        if isinstance(command, MCILDefineSort):
            # FIXME: Need to check for any Int parameters of the definition
            raise NotImplementedError
        elif isinstance(command, MCILDeclareConst) and command.sort.symbol in SORT_MAP:
            command.sort = SORT_MAP[command.sort.symbol]
        elif isinstance(command, MCILDeclareFun):
            for ivar in [i for i in command.inputs if i.identifier.symbol in SORT_MAP]:
                command.inputs[command.inputs.index(ivar)] = SORT_MAP[ivar]

            if command.output_sort.symbol in SORT_MAP:
                command.output_sort = SORT_MAP[command.output_sort.symbol]
        elif isinstance(command, MCILDefineFun):
            for var in [(symbol,sort) for symbol,sort in command.input if sort.symbol in SORT_MAP]:
                symbol,sort = var
                command.input[command.input.index(var)] = (symbol, SORT_MAP[sort])

            if command.output_sort.symbol in SORT_MAP:
                command.output_sort = SORT_MAP[command.output_sort.symbol]
        elif isinstance(command, MCILSystemCommand):
            for var in [(symbol,sort) for symbol,sort in command.input if sort in SORT_MAP]:
                symbol,sort = var
                command.input[command.input.index(var)] = (symbol, SORT_MAP[sort])
            for var in [(symbol,sort) for symbol,sort in command.output if sort in SORT_MAP]:
                symbol,sort = var
                command.output[command.output.index(var)] = (symbol, SORT_MAP[sort])
            for var in [(symbol,sort) for symbol,sort in command.local if sort in SORT_MAP]:
                symbol,sort = var
                command.local[command.local.index(var)] = (symbol, SORT_MAP[sort])

            sys_vars = [v for v in command.input_vars + command.output_vars + command.local_vars if v.sort in SORT_MAP]
            for var in sys_vars:
                var.sort = SORT_MAP[var.sort]
                command.var_sorts[var.symbol] = var.sort

        context = MCILContext()
        for expr1 in command.get_exprs():
            for expr2 in postorder_mcil(expr1, context):
                to_qfbv_expr(expr2)

