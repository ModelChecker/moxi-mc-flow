"""
Representation of MoXI
"""

from __future__ import annotations

from collections import deque
from copy import copy
from enum import Enum
from pathlib import Path
from typing import Any, Callable, Optional, cast

from src import log

FILE_NAME = Path(__file__).name


class CommandAttribute(Enum):
    INPUT = ":input"
    OUTPUT = ":output"
    LOCAL = ":local"
    INIT = ":init"
    TRANS = ":trans"
    INV = ":inv"
    SUBSYS = ":subsys"
    ASSUMPTION = ":assumption"
    FAIRNESS = ":fairness"
    REACHABLE = ":reachable"
    CURRENT = ":current"
    QUERY = ":query"
    QUERIES = ":queries"

    def is_variable_declaration(self) -> bool:
        return (
            self.value == ":input" or self.value == ":output" or self.value == ":local"
        )

    def is_definable_once(self) -> bool:
        return self.is_variable_declaration() or self.value == ":init"

    def get_value_type(self) -> type:
        if (
            self.value == ":input"
            or self.value == ":output"
            or self.value == ":local"
            or self.value == ":subsys"
            or self.value == ":assumption"
            or self.value == ":fairness"
            or self.value == ":reachable"
            or self.value == ":current"
            or self.value == ":query"
        ):
            return dict
        elif self.value == ":queries":
            return list
        elif self.value == ":init" or self.value == ":trans" or self.value == ":inv":
            return Term

        raise NotImplementedError


class Identifier:
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
        return (
            any([self.symbol == s for s in __symbols])
            and len(self.indices) == num_indices
        )

    def is_indexed(self) -> bool:
        return len(self.indices) > 0

    def is_simple(self) -> bool:
        return len(self.indices) == 0

    def is_symbol(self, __symbol: str) -> bool:
        """Returns whether identifier is not indexed and has symbol '__symbol'"""
        return not self.is_indexed() and self.symbol == __symbol

    def __eq__(self, __value: object) -> bool:
        """Two Identifiers are equal if they have the same symbol and indices."""
        if isinstance(__value, str):
            return self.is_symbol(__value)

        if not isinstance(__value, Identifier):
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
        return s[:-1] + ")"

    def to_json(self) -> dict:
        if self.is_simple():
            return {"symbol": self.symbol}
        else:
            return {"symbol": self.symbol, "indices": self.indices}


class Sort:
    def __init__(self, identifier: Identifier, sorts: list[Sort]):
        self.identifier = identifier
        self.symbol = identifier.symbol
        self.parameters = sorts

    @classmethod
    def NoSort(cls) -> Sort:
        return cls(Identifier("", []), [])

    @classmethod
    def Bool(cls) -> Sort:
        return cls(Identifier("Bool", []), [])

    @classmethod
    def Int(cls) -> Sort:
        return cls(Identifier("Int", []), [])

    @classmethod
    def Real(cls) -> Sort:
        return cls(Identifier("Real", []), [])

    @classmethod
    def BitVec(cls, width: int) -> Sort:
        return cls(Identifier("BitVec", [width]), [])

    @classmethod
    def Array(cls, index: Sort, element: Sort) -> Sort:
        return cls(Identifier("Array", []), [index, element])

    @classmethod
    def Enum(cls, symbol: str) -> Sort:
        return cls(Identifier(symbol, []), [])

    @classmethod
    def Any(cls) -> Sort:
        return cls(Identifier("__Any__", []), [])

    def arity(self) -> int:
        return len(self.parameters)

    def is_parametric(self) -> bool:
        return len(self.parameters) > 0

    def get_index(self, index: int) -> int:
        return self.identifier.indices[index]

    def __eq__(self, __value: object) -> bool:
        if not isinstance(__value, Sort):
            return False

        if is_any_sort(self) or is_any_sort(__value):
            return True

        if self.identifier != __value.identifier:
            return False

        if [s for s in self.parameters] != [s for s in __value.parameters]:
            return False

        return True

    def __hash__(self) -> int:
        # TODO: not effective for parameterized sorts
        if is_bool_sort(self):
            return hash(Identifier("BitVec", [1]))
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
        if len(self.parameters) == 0:
            return { "identifier": identifier } 
        parameters = [s.to_json() for s in self.parameters]
        return {"identifier": identifier, "parameters": parameters}


def is_bool_sort(sort: Sort) -> bool:
    """A Bool sort has an identifier that is the symbol 'Bool' and is non-parametric"""
    return sort.identifier.is_symbol("Bool") and not sort.is_parametric()


def is_bitvec_sort(sort: Sort) -> bool:
    """A bit vector sort has an identifier with the symbol 'BitVec' and is indexed with a single numeral"""
    return sort.symbol == "BitVec" and len(sort.identifier.indices) == 1


def is_int_sort(sort: Sort) -> bool:
    """An Int sort has an identifier that is the symbol 'Int' and is non-parametric"""
    return sort.identifier.is_symbol("Int") and not sort.is_parametric()


def is_real_sort(sort: Sort) -> bool:
    """An Real sort has an identifier that is the symbol 'Real' and is non-parametric"""
    return sort.identifier.is_symbol("Real") and not sort.is_parametric()


def is_array_sort(sort: Sort) -> bool:
    """An Array sort has an identifier that is the symbol 'Array' and has two parameters"""
    return sort.identifier.is_symbol("Array") and sort.arity() == 2


def is_any_sort(sort: Sort) -> bool:
    """An Any sort has an identifier that is the symbol '__Any__'"""
    return sort.identifier.is_symbol("__Any__")


class Term:
    def __init__(
        self, sort: Sort, children: list[Term], loc: Optional[log.FileLocation] = None
    ):
        self.loc = loc
        self.sort = sort
        self.children = children

        self.attrs: dict[str, str | int] = {}
        self.field: Optional[tuple[Command, str, str]] = None

        self.parents: list[Term] = []
        for child in children:
            child.parents.append(self)

    def get_sort_symbol(self) -> str:
        return self.sort.symbol

    def replace(self, new: Term) -> None:
        """Replaces `self` with `new` using `self.parents` or `self.field` if `self` is a top-level term (i.e., has no parents)."""
        if not self.parents:
            if not self.field:
                raise ValueError(f"No field set for top-level term '{self}'")

            cmd, field_name, symbol = self.field
            cmd_field = getattr(cmd, field_name)

            if isinstance(cmd_field, Term):
                setattr(cmd, field_name, new)
            elif isinstance(cmd_field, dict):
                cmd_field[symbol] = new

        for parent in self.parents:
            parent.children[parent.children.index(self)] = new
            new.parents.append(parent)

    def add_attribute(self, attr: str, arg: str | int) -> None:
        self.attrs[attr] = arg

    def __hash__(self) -> int:
        return id(self)

    def __str__(self) -> str:
        return term2str(self, with_attr=True)

    def str_no_attrs(self) -> str:
        return term2str(self, with_attr=False)

    def to_json(self) -> dict:
        return term2json(self)


class Constant(Term):
    def __init__(self, sort: Sort, value: Any, loc: Optional[log.FileLocation] = None):
        super().__init__(sort, [], loc)
        self.value = value

    @classmethod
    def Bool(cls, value: bool, loc: Optional[log.FileLocation] = None) -> Constant:
        return Constant(Sort.Bool(), value, loc)

    @classmethod
    def BitVec(
        cls, width: int, value: int, loc: Optional[log.FileLocation] = None
    ) -> Constant:
        return Constant(Sort.BitVec(width), value, loc)

    @classmethod
    def Array(
        cls,
        index: Sort,
        element: Sort,
        value: Any,
        loc: Optional[log.FileLocation] = None,
    ) -> Apply:
        return Apply(Sort.Array(index, element), Identifier("const", []), [value], loc)

    @classmethod
    def Int(cls, value: int, loc: Optional[log.FileLocation] = None) -> Constant:
        return Constant(Sort.Int(), value, loc)

    @classmethod
    def Real(cls, value: float, loc: Optional[log.FileLocation] = None) -> Constant:
        return Constant(Sort.Real(), value, loc)

    @classmethod
    def Enum(
        cls, symbol: str, value: str, loc: Optional[log.FileLocation] = None
    ) -> Constant:
        return Constant(Sort.Enum(symbol), value, loc)


class VarType(Enum):
    NONE = 0
    INPUT = 1
    OUTPUT = 2
    LOCAL = 3
    LOGIC = 4


class Variable(Term):
    """A Variable requires a sort and symbol."""

    def __init__(
        self,
        sort: Sort,
        symbol: str,
        prime: bool,
        loc: Optional[log.FileLocation] = None,
    ):
        super().__init__(sort, [], loc)
        # self.var_type = var_type
        self.symbol = symbol
        self.prime = prime

    def __eq__(self, __value: object) -> bool:
        """Two Variables are equal if they have the same symbol."""
        return (
            isinstance(__value, Variable)
            and self.symbol == __value.symbol
            and self.prime == __value.prime
        )
        # and self.var_type != __value.var_type)

    def __hash__(self) -> int:
        return hash(self.symbol)


_EMPTY_VAR = Variable(Sort.NoSort(), "", False)


class Apply(Term):
    def __init__(
        self,
        sort: Sort,
        identifier: Identifier,
        children: list[Term],
        loc: Optional[log.FileLocation] = None,
    ):
        super().__init__(sort, children, loc)
        self.identifier = identifier

    @classmethod
    def Eq(cls, args: list[Term], loc: Optional[log.FileLocation] = None) -> Apply:
        return Apply(Sort.Bool(), Identifier("=", []), args, loc)

    @classmethod
    def Not(cls, arg: Term, loc: Optional[log.FileLocation] = None) -> Apply:
        return Apply(Sort.Bool(), Identifier("not", []), [arg], loc)

    @classmethod
    def And(cls, args: list[Term], loc: Optional[log.FileLocation] = None) -> Apply:
        return Apply(Sort.Bool(), Identifier("and", []), args, loc)

    @classmethod
    def Or(cls, args: list[Term], loc: Optional[log.FileLocation] = None) -> Apply:
        return Apply(Sort.Bool(), Identifier("or", []), args, loc)

    @classmethod
    def IntNeg(cls, arg: Term, loc: Optional[log.FileLocation] = None) -> Apply:
        return Apply(Sort.Int(), Identifier("-", []), [arg], loc)

    @classmethod
    def Select(
        cls, array: Term, index: Term, loc: Optional[log.FileLocation] = None
    ) -> Apply:
        return Apply(Sort.NoSort(), Identifier("select", []), [array, index], loc)

    @classmethod
    def Store(
        cls,
        array: Term,
        index: Term,
        value: Term,
        loc: Optional[log.FileLocation] = None,
    ) -> Apply:
        return Apply(Sort.NoSort(), Identifier("store", []), [array, index, value], loc)


class LetTerm(Term):
    """LetTerm tree structure looks like:

    LetTerm
    ____|___________________________
    |        |        |            |
    v        v        v            v
    Term     Bind     Term ...     Term

    where from the right we have each bound variable term, then a dummy class to do variable binding during traversal, then the argument term. We visit these in that order when performing the standard reverse postorder traversal.
    """

    def __init__(
        self,
        sort: Sort,
        binders: list[tuple[str, Term]],
        term: Term,
        loc: Optional[log.FileLocation] = None,
    ):
        super().__init__(sort, [term, Bind()] + [b[1] for b in reversed(binders)], loc)
        self.vars = [b[0] for b in reversed(binders)]

    def get_term(self) -> Term:
        return self.children[0]

    def get_binders(self) -> list[tuple[str, Term]]:
        return [(v, e) for v, e in zip(self.vars, self.children[2:])]


class Bind(Term):
    """Class used for binding variables in `let` terms during traversal."""

    def __init__(self, loc: Optional[log.FileLocation] = None):
        super().__init__(Sort.NoSort(), [], loc)

    def get_binders(self) -> list[tuple[str, Term]]:
        if not len(self.parents) == 1:
            raise ValueError("Bind can only have 1 parent.")

        parent = self.parents[0]

        if not isinstance(parent, LetTerm):
            raise ValueError("Bind must have LetTerm parent.")

        return parent.get_binders()


def term2str(term: Term, with_attr: bool = True) -> str:
    queue: deque[tuple[bool, Term | tuple[str, Term]]] = deque()
    s = ""

    queue.append((False, term))

    while len(queue) > 0:
        (handled, cur) = queue.pop()

        if handled:
            if with_attr and isinstance(cur, Term):
                for attr, value in cur.attrs.items():
                    s += f"{attr} {value} "

            s = (s[:-1] + ") ") if isinstance(cur, (Apply, LetTerm, tuple)) else s
            continue

        # first time seeing this node
        if isinstance(cur, Apply) and cur.identifier.is_symbol("const"):
            s += f"((as {cur.identifier} {cur.sort}) "
        elif isinstance(cur, Apply):
            s += f"({cur.identifier} "
        elif isinstance(cur, LetTerm):
            s += "(let ("
        elif isinstance(cur, Bind):
            s = s[:-1] + ") "
        elif isinstance(cur, Constant) and is_bitvec_sort(cur.sort):
            width = cur.sort.identifier.indices[0]
            if width <= 64:
                format_str = f"#b{'{'}0:0{cur.sort.identifier.indices[0]}b{'}'} "
                s += format_str.format(cur.value)
            else:
                s += f"(_ bv{width} {cur.value})"
        elif isinstance(cur, Constant) and isinstance(cur.value, bool):
            s += str(cur.value).lower() + " "
        elif isinstance(cur, Constant):
            s += f"{cur.value} "
        elif isinstance(cur, Variable):
            s += f"{cur.symbol}" + ("' " if cur.prime else " ")
        elif isinstance(cur, tuple):
            (v, e) = cur
            s += f"({v} "
        else:
            s += f"{str(cur)} "

        queue.append((True, cur))

        # add children to stack
        if isinstance(cur, LetTerm):
            queue.append((False, cur.get_term()))
            queue.append((False, cur.children[1]))
            for v, e in cur.get_binders():
                queue.append((False, (v, e)))
        elif isinstance(cur, tuple):
            (_, e) = cur
            queue.append((False, e))
        else:
            for child in reversed(cur.children):
                queue.append((False, child))

    if s[-1] == " ":
        s = s[:-1]

    return s


def term2json(term: Term) -> dict:
    json_map: dict[Term, dict] = {}
    context = Context()

    for subterm in postorder(term, context):
        if subterm in json_map:
            continue

        if isinstance(subterm, Constant):
            json_map[subterm] = {
                "identifier": str(subterm)
            }
        elif isinstance(subterm, Variable):
            json_map[subterm] = {
                "identifier": subterm.symbol + ("'" if subterm.prime else "")
            }
        if isinstance(subterm, Apply) and subterm.identifier.is_symbol("const"):
            json_map[subterm] = {
                "identifier": {
                    "qualifier": "as",
                    "symbol": "const",
                    "sort": subterm.sort.to_json()
                }, 
                "args": [json_map[c] for c in subterm.children]
            }
        elif isinstance(subterm, Apply):
            json_map[subterm] = {
                "identifier": subterm.identifier.to_json(), 
                "args": [json_map[c] for c in subterm.children]
            }
        elif isinstance(subterm, LetTerm):
            json_map[subterm] = {
                "identifier": {
                    "symbol": "let",
                    "binders": [{"symbol": s, "term": json_map[t]} for s,t in subterm.get_binders()]
                },
                "args": [json_map[subterm.get_term()]]
            }

    return json_map[term]


def rename_vars(term: Term, vars: dict[Variable, Term], context: Context) -> Term:
    """Returns a copy of `term` where each `Var` present in `vars` is replaced with its mapped value. Useful for inlining function calls."""
    new_term = copy(term)

    for subterm in postorder(new_term, context):
        if subterm in vars:
            subterm.replace(vars[subterm])

    return new_term


def is_const_array_term(term: Term) -> bool:
    """Returns true if `term` is of the form: `(as const (Array X Y) x)`"""
    return (
        isinstance(term, Apply)
        and term.identifier.is_symbol("const")
        and is_array_sort(term.sort)
    )


def to_json_sorted_var(symbol: str, sort: Sort) -> dict:
    return {"symbol": symbol, "sort": sort.to_json()}


def conjoin_list(term_list: list[Term]) -> Term:
    if len(term_list) == 0:
        return Constant.Bool(True)
    elif len(term_list) == 1:
        return term_list[0]
    else:
        return Apply.And(term_list)


def disjoin_list(term_list: list[Term]) -> Term:
    if len(term_list) == 0:
        return Constant.Bool(True)
    elif len(term_list) == 1:
        return term_list[0]
    else:
        return Apply.Or(term_list)


class Command:
    def __init__(self, loc: Optional[log.FileLocation] = None) -> None:
        self.loc = loc

    def get_terms(self) -> list[Term]:
        return []

    def to_json(self) -> dict:
        return {}


class DeclareSort(Command):
    def __init__(self, symbol: str, arity: int, loc: Optional[log.FileLocation] = None):
        super().__init__(loc)
        self.symbol = symbol
        self.arity = arity

    def __str__(self) -> str:
        return f"(declare-sort {self.symbol} {self.arity})"

    def to_json(self) -> dict:
        return {"command": "declare-sort", "symbol": self.symbol, "arity": self.arity}


class DefineSort(Command):
    def __init__(
        self,
        symbol: str,
        parameters: list[str],
        definition: Sort,
        loc: Optional[log.FileLocation] = None,
    ):
        super().__init__(loc)
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
            "definition": self.definition.to_json(),
        }


class DeclareEnumSort(Command):
    def __init__(
        self, symbol: str, values: list[str], loc: Optional[log.FileLocation] = None
    ):
        super().__init__(loc)
        self.symbol = symbol
        self.values = values

    def __str__(self) -> str:
        values_str = " ".join(self.values)
        return f"(declare-enum-sort {self.symbol} ({values_str}))"

    def to_json(self) -> dict:
        return {
            "command": "declare-enum-sort",
            "symbol": self.symbol,
            "values": self.values,
        }


class DeclareConst(Command):
    def __init__(self, symbol: str, sort: Sort, loc: Optional[log.FileLocation] = None):
        super().__init__(loc)
        self.symbol = symbol
        self.sort = sort

    def __str__(self) -> str:
        return f"(declare-const {self.symbol} {self.sort})"

    def to_json(self) -> dict:
        return {
            "command": "declare-const",
            "symbol": self.symbol,
            "values": self.sort.to_json(),
        }


class DeclareFun(Command):
    def __init__(
        self,
        symbol: str,
        inputs: list[Sort],
        output: Sort,
        loc: Optional[log.FileLocation] = None,
    ) -> None:
        super().__init__(loc)
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
            "output": self.output_sort.to_json(),
        }


class DefineFun(Command):
    def __init__(
        self,
        symbol: str,
        input: list[tuple[str, Sort]],
        output: Sort,
        body: Term,
        loc: Optional[log.FileLocation] = None,
    ) -> None:
        super().__init__(loc)
        self.symbol = symbol
        self.input = input
        self.output_sort = output
        self.body = body

        self.body.field = (self, "body", "")

    def get_terms(self) -> list[Term]:
        return [self.body]

    def __str__(self) -> str:
        input_str = " ".join([f"({symbol} {sort})" for symbol, sort in self.input])
        return (
            f"(define-fun {self.symbol} ({input_str}) {self.output_sort} {self.body})"
        )

    def to_json(self) -> dict:
        return {
            "command": "define-fun",
            "symbol": self.symbol,
            "input": [to_json_sorted_var(symbol, sort) for symbol, sort in self.input],
            "output": self.output_sort.to_json(),
            "body": self.body.to_json(),
        }


class SetLogic(Command):
    def __init__(self, logic: str, loc: Optional[log.FileLocation] = None):
        super().__init__(loc)
        self.logic = logic

    def __str__(self) -> str:
        return f"(set-logic {self.logic})"

    def to_json(self) -> dict:
        return {"command": "set-logic", "logic": self.logic}


class SystemCommand(Command):
    def __init__(
        self,
        symbol: str,
        input: list[tuple[str, Sort]],
        output: list[tuple[str, Sort]],
        local: list[tuple[str, Sort]],
        loc: Optional[log.FileLocation] = None,
    ) -> None:
        super().__init__(loc)
        self.symbol = symbol
        self.input = input
        self.local = local
        self.output = output

        # this gets populated by sort checker
        self.var_sorts: dict[str, Sort] = {}

        # useful for mapping variables across subsystems
        self.input_vars = [Variable(sort, symbol, False) for symbol, sort in input]
        self.output_vars = [Variable(sort, symbol, False) for symbol, sort in output]
        self.local_vars = [Variable(sort, symbol, False) for symbol, sort in local]

        self.input_symbols = set([s for s, _ in self.input])
        self.output_symbols = set([s for s, _ in self.output])
        self.local_symbols = set([s for s, _ in self.local])

        self.signature = [s for s, _ in self.input] + [s for s, _ in self.output]
        self.full_signature = (
            [s for s, _ in self.input]
            + [s for s, _ in self.output]
            + [s for s, _ in self.local]
        )

    def get_sort(self, symbol: str) -> Optional[Sort]:
        """Returns the sort of the variable with symbol `symbol`, if there exists such a variable."""
        if symbol not in self.var_sorts:
            return None
        return self.var_sorts[symbol]


class DefineSystem(SystemCommand):
    def __init__(
        self,
        symbol: str,
        input: list[tuple[str, Sort]],
        output: list[tuple[str, Sort]],
        local: list[tuple[str, Sort]],
        init: Term,
        trans: Term,
        inv: Term,
        subsystems: dict[str, tuple[str, list[str]]],
        loc: Optional[log.FileLocation] = None,
    ):
        super().__init__(symbol, input, output, local, loc)
        self.init = init
        self.trans = trans
        self.inv = inv
        self.subsystem_signatures = subsystems

        self.init.field = (self, "init", "")
        self.trans.field = (self, "trans", "")
        self.inv.field = (self, "inv", "")

        # this gets populated by sort checker
        self.subsystems: dict[str, DefineSystem] = {}

    def get_subsys_params(self, symbol: str) -> list[str]:
        return self.subsystem_signatures[symbol][1]

    def get_terms(self) -> list[Term]:
        return [self.init, self.trans, self.inv]

    def __str__(self) -> str:
        input_str = " ".join([f"({symbol} {sort})" for symbol, sort in self.input])
        output_str = " ".join([f"({symbol} {sort})" for symbol, sort in self.output])
        local_str = " ".join([f"({symbol} {sort})" for symbol, sort in self.local])

        subsystem_str = ""
        for symbol, signature in self.subsystem_signatures.items():
            (sys_symbol, args) = signature
            subsystem_str += f"\n   :subsys ({symbol} ({sys_symbol} {' '.join(args)}))"

        s = f"(define-system {self.symbol} "
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
            "input": [to_json_sorted_var(symbol, sort) for symbol, sort in self.input],
            "output": [
                to_json_sorted_var(symbol, sort) for symbol, sort in self.output
            ],
            "local": [to_json_sorted_var(symbol, sort) for symbol, sort in self.local],
            "init": self.init.to_json(),
            "trans": self.trans.to_json(),
            "inv": self.inv.to_json(),
            "subsys": [
                {"symbol": s, "target": {"symbol": t, "arguments": v}}
                for s, (t, v) in self.subsystem_signatures.items()
            ],
        }


class CheckSystem(SystemCommand):
    def __init__(
        self,
        symbol: str,
        input: list[tuple[str, Sort]],
        output: list[tuple[str, Sort]],
        local: list[tuple[str, Sort]],
        assumption: dict[str, Term],
        fairness: dict[str, Term],
        reachable: dict[str, Term],
        current: dict[str, Term],
        query: dict[str, list[str]],
        queries: list[dict[str, list[str]]],
        loc: Optional[log.FileLocation] = None,
    ):
        super().__init__(symbol, input, output, local, loc)
        self.assumption = assumption
        self.fairness = fairness
        self.reachable = reachable
        self.current = current
        self.query = query
        self.queries = queries

        for symbol, term in assumption.items():
            term.field = (self, "assumption", symbol)
        for symbol, term in fairness.items():
            term.field = (self, "fairness", symbol)
        for symbol, term in reachable.items():
            term.field = (self, "reachable", symbol)
        for symbol, term in current.items():
            term.field = (self, "current", symbol)

    def get_terms(self) -> list[Term]:
        return (
            [a for a in self.assumption.values()]
            + [f for f in self.fairness.values()]
            + [r for r in self.reachable.values()]
            + [c for c in self.current.values()]
        )

    def __str__(self) -> str:
        input_str = " ".join([f"({symbol} {sort})" for symbol, sort in self.input])
        output_str = " ".join([f"({symbol} {sort})" for symbol, sort in self.output])
        local_str = " ".join([f"({symbol} {sort})" for symbol, sort in self.local])

        assumption_str = "".join(
            [
                f"\n   :assumption ({symbol} {term})"
                for symbol, term in self.assumption.items()
            ]
        )
        fairness_str = "".join(
            [
                f"\n   :fairness ({symbol} {term})"
                for symbol, term in self.fairness.items()
            ]
        )
        reachable_str = "".join(
            [
                f"\n   :reachable ({symbol} {term})"
                for symbol, term in self.reachable.items()
            ]
        )
        current_str = "".join(
            [
                f"\n   :current ({symbol} {term})"
                for symbol, term in self.current.items()
            ]
        )
        query_str = "".join(
            [
                f"\n   :query ({symbol} ({' '.join(labels)}))"
                for symbol, labels in self.query.items()
            ]
        )

        queries_str = ""
        for query in self.queries:
            query_list_str = " ".join(
                [f"({symbol} ({' '.join(labels)}))" for symbol, labels in query.items()]
            )
            queries_str += f"\n   :queries ({query_list_str})"

        s = f"(check-system {self.symbol} "
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
            "input": [to_json_sorted_var(symbol, sort) for symbol, sort in self.input],
            "output": [
                to_json_sorted_var(symbol, sort) for symbol, sort in self.output
            ],
            "local": [to_json_sorted_var(symbol, sort) for symbol, sort in self.local],
            "assumption": [
                {"symbol": s, "formula": a.to_json()}
                for s, a in self.assumption.items()
            ],
            "fairness": [
                {"symbol": s, "formula": f.to_json()} for s, f in self.fairness.items()
            ],
            "reachable": [
                {"symbol": s, "formula": r.to_json()} for s, r in self.reachable.items()
            ],
            "current": [
                {"symbol": s, "formula": c.to_json()} for s, c in self.current.items()
            ],
            "query": [{"symbol": s, "formulas": q} for s, q in self.query.items()],
            "queries": [
                [{"symbol": s, "formulas": q} for s, q in query.items()]
                for query in self.queries
            ],
        }


class Program:
    def __init__(self, commands: list[Command]):
        self.commands: list[Command] = commands

    def get_terms(self) -> list[Term]:
        return [t for cmd in self.commands for t in cmd.get_terms()]

    def get_check_system_cmds(self) -> list[CheckSystem]:
        return [cmd for cmd in self.commands if isinstance(cmd, CheckSystem)]

    def __str__(self) -> str:
        return "\n".join(str(cmd) for cmd in self.commands)

    def to_json(self) -> list:
        return [cmd.to_json() for cmd in self.commands]


class SetOption(Command):
    def __init__(self, option: str, loc: Optional[log.FileLocation] = None):
        super().__init__(loc)
        self.option = option

    def __str__(self) -> str:
        return f"(set-option {self.option})"


class Exit(Command):
    def __init__(self, loc: Optional[log.FileLocation] = None) -> None:
        super().__init__(loc)


def bool_const(value: bool) -> Constant:
    return Constant(Sort.Bool(), value)


# A rank is a function signature. For example:
#   rank(and) = ([Bool, Bool], Bool)
Rank = tuple[list[Sort], Sort]

# An identifier class describes a class of identifiers that have the same symbol and number of indices.
# For instance, ("BitVec", 1) describes the class of bit vector sorts and ("extract", 2) describes the
# class of all bit vector "extract" operators.
IdentifierClass = tuple[str, int]

# RankTable[f,i] = ( par A ( rank(f,A) ) )
#   where rank(f,A) is the rank of function with symbol f and number indices i given parameter(s) A
RankTable = dict[IdentifierClass, Callable[[Any], Rank]]

CORE_RANK_TABLE: RankTable = {
    ("true", 0): lambda _: ([], Sort.Bool()),
    ("false", 0): lambda _: ([], Sort.Bool()),
    ("not", 0): lambda _: ([Sort.Bool()], Sort.Bool()),
    ("=>", 0): lambda _: ([Sort.Bool(), Sort.Bool()], Sort.Bool()),
    ("and", 0): lambda A: ([Sort.Bool() for _ in range(0, A)], Sort.Bool()),
    ("or", 0): lambda A: ([Sort.Bool() for _ in range(0, A)], Sort.Bool()),
    ("xor", 0): lambda A: ([Sort.Bool() for _ in range(0, A)], Sort.Bool()),
    ("=", 0): lambda A: ([A[0] for _ in range(0, A[1])], Sort.Bool()),
    ("distinct", 0): lambda A: ([A[0] for _ in range(0, A[1])], Sort.Bool()),
    ("ite", 0): lambda A: ([Sort.Bool(), A, A], A),
    ("const", 0): lambda A: ([Sort.Any()], A),
    ("OnlyChange", 0): lambda A: ([Sort.Any() for _ in range(0, A)], Sort.Bool()),
}

BITVEC_RANK_TABLE: RankTable = {
    ("concat", 0): lambda A: (
        [Sort.BitVec(A[0]), Sort.BitVec(A[1])],
        Sort.BitVec(A[0] + A[1]),
    ),
    ("extract", 2): lambda A: ([Sort.BitVec(A[0])], Sort.BitVec(A[1])),
    ("zero_extend", 1): lambda A: ([Sort.BitVec(A[0])], Sort.BitVec(A[0] + A[1])),
    ("sign_extend", 1): lambda A: ([Sort.BitVec(A[0])], Sort.BitVec(A[0] + A[1])),
    ("rotate_left", 1): lambda A: ([Sort.BitVec(A)], Sort.BitVec(A)),
    ("rotate_right", 1): lambda A: ([Sort.BitVec(A)], Sort.BitVec(A)),
    ("bvshl", 0): lambda A: ([Sort.BitVec(A), Sort.BitVec(A)], Sort.BitVec(A)),
    ("bvlshr", 0): lambda A: ([Sort.BitVec(A), Sort.BitVec(A)], Sort.BitVec(A)),
    ("bvashr", 0): lambda A: ([Sort.BitVec(A), Sort.BitVec(A)], Sort.BitVec(A)),
    ("bvnot", 0): lambda A: ([Sort.BitVec(A)], Sort.BitVec(A)),
    ("bvneg", 0): lambda A: ([Sort.BitVec(A)], Sort.BitVec(A)),
    ("bvand", 0): lambda A: ([Sort.BitVec(A), Sort.BitVec(A)], Sort.BitVec(A)),
    ("bvnand", 0): lambda A: ([Sort.BitVec(A), Sort.BitVec(A)], Sort.BitVec(A)),
    ("bvor", 0): lambda A: ([Sort.BitVec(A), Sort.BitVec(A)], Sort.BitVec(A)),
    ("bvnor", 0): lambda A: ([Sort.BitVec(A), Sort.BitVec(A)], Sort.BitVec(A)),
    ("bvxor", 0): lambda A: ([Sort.BitVec(A), Sort.BitVec(A)], Sort.BitVec(A)),
    ("bvxnor", 0): lambda A: ([Sort.BitVec(A), Sort.BitVec(A)], Sort.BitVec(A)),
    ("bvadd", 0): lambda A: ([Sort.BitVec(A), Sort.BitVec(A)], Sort.BitVec(A)),
    ("bvsub", 0): lambda A: ([Sort.BitVec(A), Sort.BitVec(A)], Sort.BitVec(A)),
    ("bvmul", 0): lambda A: ([Sort.BitVec(A), Sort.BitVec(A)], Sort.BitVec(A)),
    ("bvudiv", 0): lambda A: ([Sort.BitVec(A), Sort.BitVec(A)], Sort.BitVec(A)),
    ("bvsdiv", 0): lambda A: ([Sort.BitVec(A), Sort.BitVec(A)], Sort.BitVec(A)),
    ("bvurem", 0): lambda A: ([Sort.BitVec(A), Sort.BitVec(A)], Sort.BitVec(A)),
    ("bvsrem", 0): lambda A: ([Sort.BitVec(A), Sort.BitVec(A)], Sort.BitVec(A)),
    ("bvsmod", 0): lambda A: ([Sort.BitVec(A), Sort.BitVec(A)], Sort.BitVec(A)),
    ("bvult", 0): lambda A: ([Sort.BitVec(A), Sort.BitVec(A)], Sort.Bool()),
    ("bvule", 0): lambda A: ([Sort.BitVec(A), Sort.BitVec(A)], Sort.Bool()),
    ("bvugt", 0): lambda A: ([Sort.BitVec(A), Sort.BitVec(A)], Sort.Bool()),
    ("bvuge", 0): lambda A: ([Sort.BitVec(A), Sort.BitVec(A)], Sort.Bool()),
    ("bvslt", 0): lambda A: ([Sort.BitVec(A), Sort.BitVec(A)], Sort.Bool()),
    ("bvsle", 0): lambda A: ([Sort.BitVec(A), Sort.BitVec(A)], Sort.Bool()),
    ("bvsgt", 0): lambda A: ([Sort.BitVec(A), Sort.BitVec(A)], Sort.Bool()),
    ("bvsge", 0): lambda A: ([Sort.BitVec(A), Sort.BitVec(A)], Sort.Bool()),
    ("reduce_and", 0): lambda A: ([Sort.BitVec(A)], Sort.Bool()),
    ("reduce_or", 0): lambda A: ([Sort.BitVec(A)], Sort.Bool()),
    ("reduce_xor", 0): lambda A: ([Sort.BitVec(A)], Sort.Bool()),
}

ARRAY_RANK_TABLE: RankTable = {
    ("select", 0): lambda A: ([Sort.Array(A[0], A[1]), A[0]], A[1]),
    ("store", 0): lambda A: (
        [Sort.Array(A[0], A[1]), A[0], A[1]],
        Sort.Array(A[0], A[1]),
    ),
}

INT_RANK_TABLE: RankTable = {
    ("-", 0): lambda A: ([Sort.Int() for _ in range(0, A)], Sort.Int()),
    ("+", 0): lambda _: ([Sort.Int(), Sort.Int()], Sort.Int()),
    ("*", 0): lambda _: ([Sort.Int(), Sort.Int()], Sort.Int()),
    ("/", 0): lambda _: ([Sort.Int(), Sort.Int()], Sort.Int()),
    ("div", 0): lambda _: ([Sort.Int(), Sort.Int()], Sort.Int()),
    ("mod", 0): lambda _: ([Sort.Int(), Sort.Int()], Sort.Int()),
    ("abs", 0): lambda _: ([Sort.Int()], Sort.Int()),
    ("<=", 0): lambda A: ([Sort.Int() for _ in range(0, A)], Sort.Bool()),
    ("<", 0): lambda A: ([Sort.Int() for _ in range(0, A)], Sort.Bool()),
    (">=", 0): lambda A: ([Sort.Int() for _ in range(0, A)], Sort.Bool()),
    (">", 0): lambda A: ([Sort.Int() for _ in range(0, A)], Sort.Bool()),
    ("divisible", 1): lambda _: ([Sort.Int()], Sort.Bool()),
}

REAL_RANK_TABLE: RankTable = {
    ("-", 0): lambda A: ([Sort.Real() for _ in range(0, A)], Sort.Real()),
    ("+", 0): lambda _: ([Sort.Real(), Sort.Real()], Sort.Real()),
    ("*", 0): lambda _: ([Sort.Real(), Sort.Real()], Sort.Real()),
    ("/", 0): lambda _: ([Sort.Real(), Sort.Real()], Sort.Real()),
    ("<=", 0): lambda A: ([Sort.Real() for _ in range(0, A)], Sort.Bool()),
    ("<", 0): lambda A: ([Sort.Real() for _ in range(0, A)], Sort.Bool()),
    (">=", 0): lambda A: ([Sort.Real() for _ in range(0, A)], Sort.Bool()),
    (">", 0): lambda A: ([Sort.Real() for _ in range(0, A)], Sort.Bool()),
}


REAL_INT_RANK_TABLE: RankTable = {
    ("to_real", 0): lambda _: ([Sort.Int()], Sort.Real()),
    ("to_int", 0): lambda _: ([Sort.Real()], Sort.Int()),
    ("is_int", 0): lambda _: ([Sort.Real()], Sort.Bool()),
}


def sort_check_apply_rank(node: Apply, rank: Rank) -> bool:
    rank_args, rank_return = rank

    if rank_args != [c.sort for c in node.children]:
        return False

    node.sort = rank_return
    return True


def sort_check_apply_core(node: Apply) -> bool:
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

        if not isinstance(node.children[0], Constant):
            return False

        rank = CORE_RANK_TABLE[identifier_class](node.sort)

        return sort_check_apply_rank(node, rank)
    elif identifier.check({"OnlyChange"}, 0):
        if len(node.children) < 1:
            return False

        if any([not isinstance(c, Variable) for c in node.children]):
            return False

        param = len(node.children)
        rank = CORE_RANK_TABLE[identifier_class](param)

        return sort_check_apply_rank(node, rank)

    rank = CORE_RANK_TABLE[identifier_class](None)
    return sort_check_apply_rank(node, rank)


def sort_check_apply_bitvec(node: Apply) -> bool:
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
        (i, j) = identifier.indices

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


def sort_check_apply_arrays(node: Apply) -> bool:
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


def sort_check_apply_int(node: Apply) -> bool:
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
        # (Op Int Int Int)
        # (Op Int Int)
        if len(node.children) < 2 or len(node.children) > 3:
            return False

        param = len(node.children)
        rank = INT_RANK_TABLE[identifier_class](param)

        return sort_check_apply_rank(node, rank)

    rank = INT_RANK_TABLE[identifier_class](None)
    return sort_check_apply_rank(node, rank)


def sort_check_apply_real(node: Apply) -> bool:
    # "-", "+", "*", "/", ">=", ">", "<=", "<"
    identifier = node.identifier
    identifier_class = identifier.get_class()

    if identifier_class not in REAL_RANK_TABLE:
        return False
    elif identifier.check({"-"}, 0):
        # (- Real Real Real)
        # (- Real Real)
        if len(node.children) < 1 or len(node.children) > 2:
            return False

        param = len(node.children)
        rank = REAL_RANK_TABLE[identifier_class](param)

        return sort_check_apply_rank(node, rank)
    elif identifier.check({">=", ">", "<=", "<"}, 0):
        # (Op Real Real Real)
        # (Op Real Real)
        if len(node.children) < 2 or len(node.children) > 3:
            return False

        param = len(node.children)
        rank = REAL_RANK_TABLE[identifier_class](param)

        return sort_check_apply_rank(node, rank)

    rank = REAL_RANK_TABLE[identifier_class](None)
    return sort_check_apply_rank(node, rank)


def sort_check_apply_real_int(node: Apply) -> bool:
    # "to_int", "to_real", "is_int"
    identifier = node.identifier
    identifier_class = identifier.get_class()

    if identifier_class not in REAL_INT_RANK_TABLE:
        return False

    rank = REAL_INT_RANK_TABLE[identifier_class](None)
    return sort_check_apply_rank(node, rank)


def sort_check_apply_all(node: Apply) -> bool:
    identifier_class = (node.identifier.symbol, node.identifier.num_indices())

    if identifier_class in CORE_RANK_TABLE:
        return sort_check_apply_core(node)
    elif identifier_class in BITVEC_RANK_TABLE:
        return sort_check_apply_bitvec(node)
    elif identifier_class in ARRAY_RANK_TABLE:
        return sort_check_apply_arrays(node)
    elif identifier_class in INT_RANK_TABLE and identifier_class in REAL_RANK_TABLE:
        return sort_check_apply_int(node) or sort_check_apply_real(node)
    elif identifier_class in INT_RANK_TABLE:
        return sort_check_apply_int(node)
    elif identifier_class in REAL_RANK_TABLE:
        return sort_check_apply_real(node)
    elif identifier_class in REAL_INT_RANK_TABLE:
        return sort_check_apply_real_int(node)

    return False


def sort_check_apply_qf_bv(node: Apply) -> bool:
    identifier_class = (node.identifier.symbol, node.identifier.num_indices())

    if identifier_class in CORE_RANK_TABLE:
        return sort_check_apply_core(node)
    elif identifier_class in BITVEC_RANK_TABLE:
        return sort_check_apply_bitvec(node)

    return False


def sort_check_apply_qf_abv(node: Apply) -> bool:
    identifier_class = (node.identifier.symbol, node.identifier.num_indices())

    if identifier_class in CORE_RANK_TABLE:
        return sort_check_apply_core(node)
    elif identifier_class in BITVEC_RANK_TABLE:
        return sort_check_apply_bitvec(node)
    elif identifier_class in ARRAY_RANK_TABLE:
        return sort_check_apply_arrays(node)

    return False


def sort_check_apply_qf_lia(node: Apply) -> bool:
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
            lhs, rhs = node.children
            if isinstance(lhs, Constant):
                # (* n x)
                if not isinstance(rhs, Variable):
                    return False
            elif isinstance(lhs, Apply):
                # (* (- n) x)
                if not lhs.identifier.check({"-"}, 0):
                    return False
                elif not len(lhs.children) == 1:
                    return False
                elif not isinstance(lhs.children[0], Constant):
                    return False
                elif not isinstance(rhs, Variable):
                    return False
            elif isinstance(rhs, Constant):
                # (* x n)
                if not isinstance(lhs, Variable):
                    return False
            elif isinstance(rhs, Apply):
                # (* x (- n))
                if not rhs.identifier.check({"-"}, 0):
                    return False
                elif not len(rhs.children) == 1:
                    return False
                elif not isinstance(rhs.children[0], Constant):
                    return False
                elif not isinstance(lhs, Variable):
                    return False

        return status

    return False


def sort_check_apply_qf_nia(node: Apply) -> bool:
    identifier_class = (node.identifier.symbol, node.identifier.num_indices())

    if identifier_class in CORE_RANK_TABLE:
        return sort_check_apply_core(node)
    elif identifier_class in INT_RANK_TABLE:
        return sort_check_apply_int(node)

    return False


def sort_check_apply_qf_lra(node: Apply) -> bool:
    identifier_class = (node.identifier.symbol, node.identifier.num_indices())

    if identifier_class in CORE_RANK_TABLE:
        return sort_check_apply_core(node)
    elif identifier_class in REAL_RANK_TABLE:
        status = sort_check_apply_real(node)

        if not status:
            return status

        # Special case for LRA (from SMT-LIB):
        # Terms with _concrete_ coefficients are also allowed, that is, terms
        # of the form c, (* c x), or (* x c)  where x is a free constant and
        # c is an integer or rational coefficient.
        # - An integer coefficient is a term of the form m or (- m) for some
        #   numeral m.
        # - A rational coefficient is a term of the form d, (- d) or (/ c n)
        #   for some decimal d, integer coefficient c and numeral n other than 0.
        if node.identifier.check({"*"}, 0):
            lhs, rhs = node.children
            if isinstance(lhs, Constant):
                # (* n x)
                if not isinstance(rhs, Variable):
                    return False
            elif isinstance(lhs, Apply):
                # (* (- n) x)
                if not lhs.identifier.check({"-"}, 0):
                    return False
                elif not len(lhs.children) == 1:
                    return False
                elif not isinstance(lhs.children[0], Constant):
                    return False
                elif not isinstance(rhs, Variable):
                    return False
            elif isinstance(rhs, Constant):
                # (* x n)
                if not isinstance(lhs, Variable):
                    return False
            elif isinstance(rhs, Apply):
                # (* x (- n))
                if not rhs.identifier.check({"-"}, 0):
                    return False
                elif not len(rhs.children) == 1:
                    return False
                elif not isinstance(rhs.children[0], Constant):
                    return False
                elif not isinstance(lhs, Variable):
                    return False
        elif node.identifier.check({"/"}, 0):
            lhs, rhs = node.children
            if isinstance(lhs, Apply):
                if not lhs.identifier.check({"-"}, 0):
                    return False
                elif not len(lhs.children) == 1:
                    return False
                elif not isinstance(lhs.children[0], Constant):
                    return False
                elif not isinstance(rhs, Variable):
                    return False
            elif isinstance(rhs, Apply):
                if not rhs.identifier.check({"-"}, 0):
                    return False
                elif not len(rhs.children) == 1:
                    return False
                elif not isinstance(rhs.children[0], Constant):
                    return False
                elif not isinstance(lhs, Variable):
                    return False

        return status

    return False


def sort_check_apply_qf_nra(node: Apply) -> bool:
    identifier_class = (node.identifier.symbol, node.identifier.num_indices())

    if identifier_class in CORE_RANK_TABLE:
        return sort_check_apply_core(node)
    elif identifier_class in REAL_RANK_TABLE:
        return sort_check_apply_real(node)

    return False


class Logic:
    """An logic has a name, a set of sort symbols, a set of function symbols, and a sort_check function"""

    def __init__(
        self,
        symbol: str,
        sort_symbols: set[IdentifierClass],
        function_symbols: set[IdentifierClass],
        sort_check: Callable[[Apply], bool],
        uf: bool
    ):
        self.symbol = symbol
        self.sort_symbols = sort_symbols
        self.function_symbols = function_symbols
        self.sort_check = sort_check
        self.uf = uf

        self.symbols = sort_symbols | function_symbols


NO_LOGIC = Logic(
    "Not Set", {("Bool", 0)}, set(CORE_RANK_TABLE.keys()), sort_check_apply_core, False
)

ALL = Logic(
    "All",
    {("Bool", 0), ("BitVec", 1), ("Array", 0), ("Int", 0), ("Real", 0)},
    CORE_RANK_TABLE.keys()
    | BITVEC_RANK_TABLE.keys()
    | ARRAY_RANK_TABLE.keys()
    | INT_RANK_TABLE.keys()
    | REAL_RANK_TABLE.keys()
    | REAL_INT_RANK_TABLE.keys(),
    sort_check_apply_all,
    True
)

QF_BV = Logic(
    "QF_BV",
    {("Bool", 0), ("BitVec", 1)},
    CORE_RANK_TABLE.keys() | BITVEC_RANK_TABLE.keys(),
    sort_check_apply_qf_bv,
    False
)

QF_UFBV = Logic(
    "QF_UFBV",
    {("Bool", 0), ("BitVec", 1)},
    CORE_RANK_TABLE.keys() | BITVEC_RANK_TABLE.keys(),
    sort_check_apply_qf_bv,
    True
)

QF_ABV = Logic(
    "QF_ABV",
    {("Bool", 0), ("BitVec", 1), ("Array", 0)},
    CORE_RANK_TABLE.keys() | BITVEC_RANK_TABLE.keys() | ARRAY_RANK_TABLE.keys(),
    sort_check_apply_qf_abv,
    False
)

QF_AUFBV = Logic(
    "QF_AUFBV",
    {("Bool", 0), ("BitVec", 1), ("Array", 0)},
    CORE_RANK_TABLE.keys() | BITVEC_RANK_TABLE.keys() | ARRAY_RANK_TABLE.keys(),
    sort_check_apply_qf_abv,
    True
)

QF_LIA = Logic(
    "QF_LIA",
    {("Bool", 0), ("Int", 0)},
    CORE_RANK_TABLE.keys() | INT_RANK_TABLE.keys(),
    sort_check_apply_qf_lia,
    False
)

QF_NIA = Logic(
    "QF_NIA",
    {("Bool", 0), ("Int", 0)},
    CORE_RANK_TABLE.keys() | INT_RANK_TABLE.keys(),
    sort_check_apply_qf_nia,
    False
)

QF_UFLIA = Logic(
    "QF_UFLIA",
    {("Bool", 0), ("Int", 0)},
    CORE_RANK_TABLE.keys() | INT_RANK_TABLE.keys(),
    sort_check_apply_qf_lia,
    True
)

QF_UFNIA = Logic(
    "QF_UFNIA",
    {("Bool", 0), ("Int", 0)},
    CORE_RANK_TABLE.keys() | INT_RANK_TABLE.keys(),
    sort_check_apply_qf_nia,
    True
)

QF_LRA = Logic(
    "QF_LRA",
    {("Bool", 0), ("Int", 0), ("Real", 0)},
    CORE_RANK_TABLE.keys() | REAL_RANK_TABLE.keys(),
    sort_check_apply_qf_lra,
    False
)

QF_NRA = Logic(
    "QF_NRA",
    {("Bool", 0), ("Int", 0), ("Real", 0)},
    CORE_RANK_TABLE.keys() | REAL_RANK_TABLE.keys(),
    sort_check_apply_qf_nra,
    False
)

LOGIC_TABLE: dict[str, Logic] = {
    "ALL": ALL,
    "QF_BV": QF_BV,
    "QF_ABV": QF_ABV,
    "QF_LIA": QF_LIA,
    "QF_NIA": QF_NIA,
    "QF_LRA": QF_LRA,
    "QF_NRA": QF_NRA,
}


class SystemContext:
    def __init__(self):
        self._system_stack: list[tuple[str, SystemCommand]] = []

    def push(self, new: tuple[str, SystemCommand]):
        self._system_stack.append(new)

    def pop(self) -> tuple[str, SystemCommand]:
        return self._system_stack.pop()

    def copy(self) -> SystemContext:
        new_system_stack = self._system_stack.copy()
        new = SystemContext()
        for s in new_system_stack:
            new.push(s)
        return new

    def get_top(self) -> Optional[tuple[str, SystemCommand]]:
        """Returns the system at the top of the stack."""
        if len(self._system_stack) == 0:
            return None
        return self._system_stack[-1]

    def get_bottom(self) -> Optional[tuple[str, SystemCommand]]:
        """Returns the system at the bottom of the stack (top-level system)."""
        if len(self._system_stack) == 0:
            return None
        return self._system_stack[0]

    def get_subsystems(self) -> list[tuple[str, SystemCommand]]:
        if len(self._system_stack) < 3:
            return []
        return self._system_stack[2:]

    def get_input_symbols(self) -> set[str]:
        top = self.get_top()
        if not top:
            raise KeyError("No system in context")
        (_, system) = top
        return system.input_symbols

    def get_output_symbols(self) -> set[str]:
        top = self.get_top()
        if not top:
            raise KeyError("No system in context")
        (_, system) = top
        return system.output_symbols

    def get_local_symbols(self) -> set[str]:
        top = self.get_top()
        if not top:
            raise KeyError("No system in context")
        (_, system) = top
        return system.local_symbols

    def get_sort(self, symbol: str) -> Sort:
        top = self.get_top()
        if not top:
            raise KeyError("No system in context")
        (_, system) = top
        sort = system.get_sort(symbol)
        if not sort:
            raise KeyError(symbol)
        return sort

    def get_scope_symbols(self) -> list[str]:
        if len(self._system_stack) < 2:
            return []
        top_level = self._system_stack[1]
        top_level_symbol, _ = top_level
        return [top_level_symbol] + [name for name, _ in self.get_subsystems()]

    def __eq__(self, __o: object) -> bool:
        if not isinstance(__o, SystemContext):
            return False

        if len(__o._system_stack) != len(self._system_stack):
            return False

        for s1, s2 in zip(__o._system_stack, self._system_stack):
            if s1 != s2:
                return False

        return True

    def __hash__(self) -> int:
        # this works due to assumption of a dependency graph;
        # there is only one unique order for each system context
        return sum([hash(name) + hash(sys.symbol) for name, sys in self._system_stack])

    def __str__(self) -> str:
        return f"[{', '.join([f'({sym}, {sys.symbol})' for sym,sys in self._system_stack])}]"


# A RenameMap maps variables in a system context to another variable and system context. This is used for mapping
# input/output variables of subsystem. The mapped-to variable/system context pair may also be in the rename map, in
# which case another lookup is necessary.
RenameMap = dict[tuple[str, SystemContext], tuple[str, SystemContext]]


def get_scoped_var_symbol(var_symbol: str, system_context: SystemContext) -> str:
    return "::".join(system_context.get_scope_symbols() + [var_symbol])


class Context:
    def __init__(self):
        self.declared_sorts: dict[Identifier, int] = {}
        self.declared_enum_sorts: dict[str, list[str]] = {}
        self.defined_sorts: set[Sort] = set()
        self.sorts: dict[str, Sort] = {}
        self.sort_symbols: set[str] = set()

        self.declared_functions: dict[str, Rank] = {}
        self.defined_functions: dict[str, tuple[Rank, Term]] = {}
        self.defined_function_input_vars: dict[str, list[Variable]] = {}

        self.declared_consts: dict[str, Sort] = {}

        self.defined_systems: dict[str, DefineSystem] = {}
        self.system_context = SystemContext()
        self.cur_check_system: Optional[CheckSystem] = None
        self.rename_map: RenameMap = {}

        self.input_vars: set[str] = set()
        self.output_vars: set[str] = set()
        self.local_vars: set[str] = set()
        self.var_sorts: dict[str, Sort] = {}

        self.bound_let_vars: dict[str, Term] = {}

        self.cur_command: Optional[Command] = None

        self.const_arrays: set[tuple[Sort, Constant, Term]] = set()

        self.symbols: set[str] = set()

        self.set_logic(NO_LOGIC)

    def set_logic(self, logic: Logic) -> None:
        # remove symbols from previous logic
        for symbol, _ in logic.function_symbols | logic.sort_symbols:
            self.sort_symbols.discard(symbol)
            self.symbols.discard(symbol)

        # TODO: Check for conflicts between symbols and logic symbols

        self.logic = logic
        self.symbols.update([symbol for symbol, _ in logic.sort_symbols])
        self.sort_symbols.update([symbol for symbol, _ in logic.sort_symbols])
        self.symbols.update([symbol for symbol, _ in logic.function_symbols])

    def add_declared_sort(self, ident: Identifier, arity: int) -> None:
        self.declared_sorts[ident] = arity
        self.symbols.add(ident.symbol)
        self.sorts[ident.symbol] = Sort(ident, [])

    def add_declared_enum_sort(self, symbol: str, vals: list[str]) -> None:
        self.declared_enum_sorts[symbol] = vals
        self.defined_sorts.add(Sort.Enum(symbol))
        self.sort_symbols.add(symbol)
        self.symbols.add(symbol)
        [self.symbols.add(v) for v in vals]

    def add_defined_sort(self, sort: Sort) -> None:
        self.defined_sorts.add(sort)
        self.sort_symbols.add(sort.symbol)
        self.symbols.add(sort.symbol)

    def add_declared_function(self, symbol: str, rank: Rank) -> None:
        self.declared_functions[symbol] = rank
        self.symbols.add(symbol)

    def add_defined_function(self, define_fun: DefineFun) -> None:
        symbol = define_fun.symbol

        input_sorts = [sort for _, sort in define_fun.input]
        signature = (Rank((input_sorts, define_fun.output_sort)), define_fun.body)
        input_vars = [Variable(sort, sym, False) for sym, sort in define_fun.input]

        self.defined_functions[symbol] = signature
        self.defined_function_input_vars[symbol] = input_vars
        self.symbols.add(symbol)

    def add_declared_const(self, symbol: str, sort: Sort) -> None:
        self.declared_consts[symbol] = sort
        self.symbols.add(symbol)

    def add_defined_system(self, symbol: str, system: DefineSystem) -> None:
        self.defined_systems[symbol] = system
        self.symbols.add(symbol)

    def add_bound_let_var(self, symbol: str, term: Term) -> None:
        self.bound_let_vars[symbol] = term
        self.symbols.add(symbol)

    def remove_bound_let_var(self, symbol: str) -> None:
        if symbol in self.bound_let_vars:
            del self.bound_let_vars[symbol]
            self.symbols.remove(symbol)

    def add_vars(self, vars: list[tuple[str, Sort]]) -> None:
        self.var_sorts.update({symbol: sort for symbol, sort in vars})
        self.symbols.update([symbol for symbol, _ in vars])

    def remove_vars(self, vars: list[tuple[str, Sort]]) -> None:
        for symbol, _ in vars:
            del self.var_sorts[symbol]
            self.symbols.discard(symbol)

    def set_system_vars(
        self,
        input: list[tuple[str, Sort]],
        output: list[tuple[str, Sort]],
        local: list[tuple[str, Sort]],
    ) -> None:
        self.input_vars = set([symbol for symbol, _ in input])
        self.output_vars = set([symbol for symbol, _ in output])
        self.local_vars = set([symbol for symbol, _ in local])

        self.add_vars(input + output + local)

    def push_system(
        self, symbol: str, new_system: SystemCommand, params: list[str]
    ) -> None:
        # Remove symbols from current top of system stack and maintain rename_map
        top = self.system_context.get_top()
        if top:
            (_, cur_system) = top
            self.remove_vars(cur_system.input + cur_system.output + cur_system.local)
            self.update_rename_map(params, new_system, symbol)

        self.set_system_vars(new_system.input, new_system.output, new_system.local)

        self.system_context.push((symbol, new_system))

    def pop_system(self) -> tuple[str, SystemCommand]:
        old_symbol, old_system = self.system_context.pop()

        # Remove symbols from current top of system stack and maintain rename_map
        self.remove_vars(old_system.input + old_system.output + old_system.local)

        top = self.system_context.get_top()
        if top:
            (cs, cur_system) = top
            self.set_system_vars(cur_system.input, cur_system.output, cur_system.local)
        elif self.cur_check_system:
            pass

        return (old_symbol, old_system)

    def lookup_var(
        self, symbol: str, system_context: SystemContext
    ) -> tuple[str, SystemContext]:
        """Returns the variable symbol and system context that `symbol`/`system_context` point to via `rename_map`."""
        cur_var, cur_system_context = symbol, system_context
        while (cur_var, cur_system_context) in self.rename_map:
            (cur_var, cur_system_context) = self.rename_map[
                (cur_var, cur_system_context)
            ]
        return (cur_var, cur_system_context)

    def update_rename_map(
        self,
        signature: list[str],
        target_system: SystemCommand,
        target_system_symbol: str,
    ) -> None:
        target_context = (
            self.system_context.copy()
        )  # need to copy (only copies pointers)
        target_context.push((target_system_symbol, target_system))

        top = self.system_context.get_top()
        if not top:
            return

        (cur_symbol, cur_system) = top

        # If we are mapping check-system to define-system variables,
        # then we need to map each input, output, and local.
        # If we are mapping define-system to define-system variables,
        # then we only need to map each input and output.
        if isinstance(cur_system, CheckSystem):
            target_signature = target_system.full_signature
        else:
            target_signature = target_system.signature

        for cmd_var, target_var in zip(signature, target_signature):
            self.rename_map[(target_var, target_context)] = (
                cmd_var,
                self.system_context.copy(),
            )


def postorder(term: Term, context: Context):
    """Perform an iterative postorder traversal of `term`, maintaining `context`."""
    stack: list[tuple[bool, Term]] = []
    stack.append((False, term))

    while len(stack) > 0:
        (seen, cur) = stack.pop()

        if seen and isinstance(cur, LetTerm):
            for v, e in cur.get_binders():
                context.remove_bound_let_var(v)
            yield cur
        elif seen and isinstance(cur, Bind):
            for v, e in cur.get_binders():
                context.add_bound_let_var(v, e)
        elif seen:
            yield cur
        else:
            stack.append((True, cur))
            for child in cur.children:
                stack.append((False, child))


def remove_term_attrs(term: Term, context: Context):
    """Removes all attributes from `term` and all sub-terms of `term`."""
    for t in postorder(term, context):
        t.attrs = {}


def sort_check(program: Program) -> tuple[bool, Context]:
    context: Context = Context()
    status: bool = True

    def sort_check_term(
        node: Term, context: Context, no_prime: bool, is_init_term: bool
    ) -> bool:
        """Return true if node is well-sorted where `no_prime` is true if primed variables are disabled and `prime_input` is true if input variable are allowed to be primed (true for check-system assumptions and reachability conditions)."""
        # print("-------------------")
        # print(node)
        # print("-------------------")
        for term in postorder(node, context):
            # print(term)

            if isinstance(term, Constant):
                if term.sort.symbol not in context.sort_symbols:
                    log.error(
                        f"Unrecognized sort '{term.sort}' ({term}).\n\t"
                        f"Current logic: {context.logic.symbol}",
                        FILE_NAME,
                        term.loc,
                    )
                    return False

                if is_int_sort(term.sort) and context.logic in {QF_LRA, QF_NRA}:
                    term.sort = Sort.Real()
                    term.value = float(term.value)
            elif isinstance(term, Variable) and term.symbol in context.input_vars:
                term.sort = context.var_sorts[term.symbol]

                if term.sort.symbol not in context.sort_symbols:
                    log.error(
                        f"Unrecognized sort '{term.sort}' ({term}).\n\t"
                        f"Current logic: {context.logic.symbol}",
                        FILE_NAME,
                        term.loc,
                    )
                    return False

                if term.prime and no_prime:
                    log.error(
                        f"Primed variables only allowed in system transition or invariant relation ({term.symbol}).",
                        FILE_NAME,
                        term.loc,
                    )
                    return False
            elif isinstance(term, Variable) and term.symbol in context.output_vars:
                term.sort = context.var_sorts[term.symbol]

                if term.sort.symbol not in context.sort_symbols:
                    log.error(
                        f"Unrecognized sort '{term.sort}' ({term}).\n\t"
                        f"Current logic: {context.logic.symbol}",
                        FILE_NAME,
                        term.loc,
                    )
                    return False

                if term.prime and no_prime:
                    log.error(
                        f"primed variables only allowed in system transition or invariant relation ({term.symbol}).",
                        FILE_NAME,
                        term.loc,
                    )
                    return False
            elif isinstance(term, Variable) and term.symbol in context.local_vars:
                term.sort = context.var_sorts[term.symbol]

                if term.sort.symbol not in context.sort_symbols:
                    log.error(
                        f"Unrecognized sort '{term.sort}' ({term}).\n\t"
                        f"Current logic: {context.logic.symbol}",
                        FILE_NAME,
                        term.loc,
                    )
                    return False

                if term.prime and no_prime:
                    log.error(
                        f"primed variables only allowed in system transition or invariant relation ({term.symbol}).",
                        FILE_NAME,
                        term.loc,
                    )
                    return False
            elif isinstance(term, Variable) and term.symbol in context.bound_let_vars:
                if term.prime:
                    log.error(
                        f"bound variables cannot be primed ({term})",
                        FILE_NAME,
                        term.loc,
                    )
                    return False

                term.sort = context.bound_let_vars[term.symbol].sort
            elif isinstance(term, Variable) and term.symbol in context.var_sorts:
                if term.prime:
                    log.error(
                        f"only system variables be primed ({term})", FILE_NAME, term.loc
                    )
                    return False

                term.sort = context.var_sorts[term.symbol]

                if term.sort.symbol not in context.sort_symbols:
                    log.error(
                        f"Unrecognized sort '{term.sort}' ({term}).\n\t"
                        f"Current logic: {context.logic.symbol}",
                        FILE_NAME,
                        term.loc,
                    )
                    return False
            elif isinstance(term, Variable) and term.symbol in context.declared_consts:
                if term.prime:
                    log.error(f"consts cannot be primed ({term})", FILE_NAME, term.loc)
                    return False

                term.sort = context.declared_consts[term.symbol]
            elif (
                isinstance(term, Variable) and term.symbol in context.defined_functions
            ):
                if term.prime:
                    log.error(f"consts cannot be primed ({term})", FILE_NAME, term.loc)
                    return False

                # constants defined using define-fun
                ((inputs, output), _) = context.defined_functions[term.symbol]

                if len(inputs) != 0:
                    log.error(
                        f"function signature does not match definition.\n\t{term}\n\t{term.symbol}",
                        FILE_NAME,
                        term.loc,
                    )
                    return False

                term.sort = output
            elif isinstance(term, Variable):
                log.error(
                    f"symbol '{term.symbol}' not declared.",
                    FILE_NAME,
                    term.loc,
                )
                return False
            elif isinstance(term, Apply):
                if term.identifier.get_class() in context.logic.function_symbols:
                    if not context.logic.sort_check(term):
                        log.error(
                            f"function signature does not match definition.\n\t"
                            f"{term}\n\t"
                            f"{term.identifier} {[str(a.sort) for a in term.children]}",
                            FILE_NAME,
                            term.loc,
                        )
                        return False
                elif term.identifier.symbol in context.defined_functions:
                    (rank, _) = context.defined_functions[term.identifier.symbol]

                    if not sort_check_apply_rank(term, rank):
                        log.error(
                            f"function call does not match definition.\n\t{term}\n\t{term.identifier} {[str(a.sort) for a in term.children]}",
                            FILE_NAME,
                            term.loc,
                        )
                        return False
                elif term.identifier.symbol in context.declared_functions:
                    rank = context.declared_functions[term.identifier.symbol]

                    if not sort_check_apply_rank(term, rank):
                        log.error(
                            f"function call does not match definition.\n\t{term}\n\t{term.identifier} {[str(a.sort) for a in term.children]}",
                            FILE_NAME,
                            term.loc,
                        )
                        return False
                else:
                    log.error(
                        f"symbol '{term.identifier.symbol}' not recognized ({term}).",
                        FILE_NAME,
                        term.loc,
                    )
                    return False

                # constant arrays must be handled separately, maintain a list of
                # them
                if is_const_array_term(term):
                    # this is a safe cast since term is well-sorted, see sort check
                    # of "const" in sort_check_apply_core
                    const_term = cast(Constant, term.children[0])
                    context.const_arrays.add((term.sort, const_term, term))
            elif isinstance(term, LetTerm):
                # TODO: check for variable name clashes
                term.sort = term.get_term().sort
            else:
                log.error(
                    f"term type '{term.__class__}' not recognized ({term}).",
                    FILE_NAME,
                    term.loc,
                )
                return False

        return True

    # end sort_check_term

    for cmd in program.commands:
        context.cur_command = cmd

        if isinstance(cmd, SetLogic):
            if cmd.logic not in LOGIC_TABLE:
                log.error(f"logic {cmd.logic} unsupported.", FILE_NAME, cmd.loc)
                status = False
            else:
                context.set_logic(LOGIC_TABLE[cmd.logic])
        elif isinstance(cmd, DeclareSort):
            # TODO: move this warning to moxi2btor.py
            log.error(
                "Warning: declare-sort command unsupported, ignoring.",
                FILE_NAME,
                cmd.loc,
            )
        elif isinstance(cmd, DefineSort):
            if cmd.symbol in context.symbols:
                log.error(
                    f"symbol '{cmd.symbol}' already in use.",
                    FILE_NAME,
                    cmd.loc,
                )
                status = False

            # TODO
            context.add_defined_sort(cmd.definition)
        elif isinstance(cmd, DeclareEnumSort):
            for conflict in [
                s for s in [cmd.symbol] + cmd.values if s in context.symbols
            ]:
                log.error(
                    f"symbol '{conflict}' already in use.",
                    FILE_NAME,
                    cmd.loc,
                )
                status = False

            context.add_declared_enum_sort(cmd.symbol, cmd.values)
        elif isinstance(cmd, DeclareConst):
            if cmd.symbol in context.symbols:
                log.error(
                    f"symbol '{cmd.symbol}' already in use.",
                    FILE_NAME,
                    cmd.loc,
                )
                status = False

            context.add_declared_const(cmd.symbol, cmd.sort)
        elif isinstance(cmd, DeclareFun):
            if not context.logic.uf:
                log.error(
                    f"active logic ({context.logic.symbol}) does not support uninterpreted functions.",
                    FILE_NAME,
                    cmd.loc,
                )
                status = False

            if cmd.symbol in context.symbols:
                log.error(
                    f"symbol '{cmd.symbol}' already in use.",
                    FILE_NAME,
                    cmd.loc,
                )
                status = False

            context.add_declared_function(
                cmd.symbol, Rank((cmd.inputs, cmd.output_sort))
            )
        elif isinstance(cmd, DefineFun):
            if cmd.symbol in context.symbols:
                log.error(
                    f"symbol '{cmd.symbol}' already in use.",
                    FILE_NAME,
                    cmd.loc,
                )
                status = False

            context.add_vars(cmd.input)

            status = status and sort_check_term(
                cmd.body, context, no_prime=True, is_init_term=False
            )

            context.remove_vars(cmd.input)

            context.add_defined_function(cmd)
        elif isinstance(cmd, DefineSystem):
            # TODO: check for variable name clashes across cmd.input, cmd.output, cmd.local
            # TODO: check for valid sort symbols
            context.push_system(cmd.symbol, cmd, [])
            # context.add_system_vars(cmd.input, cmd.output, cmd.local)

            status = status and sort_check_term(
                cmd.init, context, no_prime=True, is_init_term=True
            )
            status = status and sort_check_term(
                cmd.trans, context, no_prime=False, is_init_term=False
            )
            status = status and sort_check_term(
                cmd.inv, context, no_prime=False, is_init_term=False
            )

            for name, subsystem in cmd.subsystem_signatures.items():
                # TODO: check for cycles in system dependency graph
                (sys_symbol, signature_symbols) = subsystem

                if sys_symbol not in context.defined_systems:
                    log.error(
                        f"system '{sys_symbol}' not defined in context.",
                        FILE_NAME,
                        cmd.loc,
                    )
                    status = False
                    return (False, context)

                # check that each symbol in signature is in the context
                signature: list[tuple[str, Sort]] = []
                for symbol in signature_symbols:
                    if symbol not in context.var_sorts:
                        log.error(
                            f"variable '{symbol}' not declared.",
                            FILE_NAME,
                            cmd.loc,
                        )
                        status = False
                        signature.append(("", Sort.NoSort()))
                        continue

                    signature.append((symbol, context.var_sorts[symbol]))

                target_system = context.defined_systems[sys_symbol]
                target_signature = target_system.input + target_system.output

                if len(signature) != len(target_signature):
                    log.error(
                        f"subsystem signature does not match target system ({sys_symbol})."
                        f"\n\t{', '.join([f'({v}: {s})' for v,s in context.defined_systems[sys_symbol].input])}"
                        f"\n\t{', '.join([f'({v}: {s})' for v,s in context.defined_systems[sys_symbol].output])}",
                        FILE_NAME,
                        cmd.loc,
                    )
                    status = False
                    continue

                for (_, cmd_sort), (_, target_sort) in zip(signature, target_signature):
                    if cmd_sort != target_sort:
                        log.error(
                            f"subsystem signature does not match target system ({sys_symbol})."
                            f"\n\t{', '.join([f'({v}: {s})' for v,s in context.defined_systems[sys_symbol].input])}"
                            f"\n\t{', '.join([f'({v}: {s})' for v,s in context.defined_systems[sys_symbol].output])}",
                            FILE_NAME,
                            cmd.loc,
                        )
                        status = False
                        continue

                cmd.subsystems[name] = context.defined_systems[sys_symbol]

            context.defined_systems[cmd.symbol] = cmd
            cmd.var_sorts.update(
                {symbol: sort for symbol, sort in cmd.input + cmd.output + cmd.local}
            )

            context.pop_system()
        elif isinstance(cmd, CheckSystem):
            if cmd.symbol not in context.defined_systems:
                log.error(f"system '{cmd.symbol}' undefined.", FILE_NAME, cmd.loc)
                status = False
                continue

            context.push_system(cmd.symbol, cmd, [])
            system = context.defined_systems[cmd.symbol]

            if len(system.input) != len(cmd.input):
                log.error(
                    f"input variables do not match target system ({system.symbol})."
                    f"\n\t{', '.join([f'({v}: {s})' for v,s in system.input])}"
                    f"\n\t{', '.join([f'({v}: {s})' for v,s in cmd.input])}",
                    FILE_NAME,
                    cmd.loc,
                )
                status = False
                continue

            for (_, sort1), (_, sort2) in zip(system.input, cmd.input):
                if sort1 != sort2:
                    log.error(
                        f"sorts do not match in check-system (expected {sort1}, got {sort2})",
                        FILE_NAME,
                        cmd.loc,
                    )
                    status = False
                else:
                    pass
                    # i2.var_type = VarType.INPUT
                # cmd.rename_map[v1] = v2

            if len(system.output) != len(cmd.output):
                log.error(
                    f"output variables do not match target system ({system.symbol})."
                    f"\n\t{', '.join([f'({v}: {s})' for v,s in system.output])}"
                    f"\n\t{', '.join([f'({v}: {s})' for v,s in cmd.output])}",
                    FILE_NAME,
                    cmd.loc,
                )
                status = False
                continue

            for (_, sort1), (_, sort2) in zip(system.output, cmd.output):
                if sort1 != sort2:
                    log.error(
                        f"sorts do not match in check-system (expected {sort1}, got {sort2})",
                        FILE_NAME,
                        cmd.loc,
                    )
                    status = False
                else:
                    pass
                # cmd.rename_map[v1] = v2

            if len(system.local) != len(cmd.local):
                log.error(
                    f"local variables do not match target system ({system.symbol})."
                    f"\n\t{', '.join([f'({v}: {s})' for v,s in system.local])}"
                    f"\n\t{', '.join([f'({v}: {s})' for v,s in cmd.local])}",
                    FILE_NAME,
                    cmd.loc,
                )
                status = False
                continue

            for (_, sort1), (_, sort2) in zip(system.local, cmd.local):
                if sort1 != sort2:
                    log.error(
                        f"sorts do not match in check-system (expected {sort1}, got {sort2})",
                        FILE_NAME,
                        cmd.loc,
                    )
                    status = False
                else:
                    pass
                # cmd.rename_map[v1] = v2

            for term in cmd.assumption.values():
                status = status and sort_check_term(
                    term, context, False, is_init_term=False
                )

            for term in cmd.reachable.values():
                status = status and sort_check_term(
                    term, context, False, is_init_term=False
                )

            for term in cmd.fairness.values():
                status = status and sort_check_term(
                    term, context, False, is_init_term=False
                )

            for term in cmd.current.values():
                status = status and sort_check_term(
                    term, context, False, is_init_term=False
                )

            cmd.var_sorts.update(
                {symbol: sort for symbol, sort in cmd.input + cmd.output + cmd.local}
            )

            context.pop_system()
        elif isinstance(cmd, Exit):
            return (status, context)
        else:
            raise NotImplementedError

    return (status, context)


def inline_funs(program: Program, context: Context) -> None:
    """Perform function inlining on each term in `program`."""
    for top_term in program.get_terms():
        for term in postorder(top_term, context):
            if (
                isinstance(term, Apply)
                and term.identifier.symbol in context.defined_functions
            ):
                fun_symbol = term.identifier.symbol

                _, fun_def = context.defined_functions[fun_symbol]
                fun_def_input_vars = context.defined_function_input_vars[fun_symbol]

                var_map = {
                    arg: val for arg, val in zip(fun_def_input_vars, term.children)
                }

                term.replace(rename_vars(fun_def, var_map, context))


def to_binary_applys(program: Program, context: Context) -> None:
    """Replace all multi-arity functions (=, and, or, <, etc.) to binary versions."""
    for top_term in program.get_terms():
        for term in postorder(top_term, context):
            if (
                isinstance(term, Apply)
                and term.identifier.check({"and", "or", "xor", "=", "distinct"}, 0)
                and len(term.children) > 2
            ):
                new_term = Apply(
                    term.sort, term.identifier, [term.children[-2], term.children[-1]]
                )
                for i in range(3, len(term.children) + 1):
                    new_term = Apply(
                        term.sort, term.identifier, [term.children[-i], new_term]
                    )

                term.replace(new_term)
            elif (
                isinstance(term, Apply)
                and term.identifier.check({"<=", "<", ">=", ">"}, 0)
                and len(term.children) == 3
            ):
                new_term = Apply(
                    term.sort,
                    term.identifier,
                    [
                        term.children[0],
                        Apply(
                            term.sort,
                            term.identifier,
                            [term.children[1], term.children[2]],
                        ),
                    ],
                )

                term.replace(new_term)


def to_qfbv(program: Program, int_width: int):
    SORT_MAP: dict[Sort, Sort] = {Sort.Int(): Sort.BitVec(int_width)}

    UNARY_OPERATOR_MAP = {
        "-": Identifier("bvneg", []),
    }

    BINARY_OPERATOR_MAP = {
        "+": Identifier("bvadd", []),
        "-": Identifier("bvsub", []),
        "*": Identifier("bvmul", []),
        "%": Identifier("bvsmod", []),
        "/": Identifier("bvsdiv", []),
        ">": Identifier("bvsgt", []),
        "<": Identifier("bvslt", []),
        ">=": Identifier("bvsge", []),
        "<=": Identifier("bvsle", []),
    }

    def to_qfbv_term(term: Term):
        if isinstance(term, Apply):
            if len(term.children) == 1 and term.identifier.symbol in UNARY_OPERATOR_MAP:
                term.identifier = UNARY_OPERATOR_MAP[term.identifier.symbol]
            elif (
                len(term.children) == 2
                and term.identifier.symbol in BINARY_OPERATOR_MAP
            ):
                term.identifier = BINARY_OPERATOR_MAP[term.identifier.symbol]

        if term.sort in SORT_MAP:
            term.sort = SORT_MAP[term.sort]

    for command in program.commands:
        if isinstance(command, SetLogic):
            command.logic = "QF_ABV"
        if isinstance(command, DefineSort):
            # FIXME: Need to check for any Int parameters of the definition
            pass
        elif isinstance(command, DeclareConst) and command.sort.symbol in SORT_MAP:
            command.sort = SORT_MAP[command.sort.symbol]
        elif isinstance(command, DeclareFun):
            for ivar in [i for i in command.inputs if i.identifier.symbol in SORT_MAP]:
                command.inputs[command.inputs.index(ivar)] = SORT_MAP[ivar]

            if command.output_sort.symbol in SORT_MAP:
                command.output_sort = SORT_MAP[command.output_sort.symbol]
        elif isinstance(command, DefineFun):
            for var in [
                (symbol, sort)
                for symbol, sort in command.input
                if sort.symbol in SORT_MAP
            ]:
                symbol, sort = var
                command.input[command.input.index(var)] = (symbol, SORT_MAP[sort])

            if command.output_sort.symbol in SORT_MAP:
                command.output_sort = SORT_MAP[command.output_sort.symbol]
        elif isinstance(command, SystemCommand):
            for var in [
                (symbol, sort) for symbol, sort in command.input if sort in SORT_MAP
            ]:
                symbol, sort = var
                command.input[command.input.index(var)] = (symbol, SORT_MAP[sort])
            for var in [
                (symbol, sort) for symbol, sort in command.output if sort in SORT_MAP
            ]:
                symbol, sort = var
                command.output[command.output.index(var)] = (symbol, SORT_MAP[sort])
            for var in [
                (symbol, sort) for symbol, sort in command.local if sort in SORT_MAP
            ]:
                symbol, sort = var
                command.local[command.local.index(var)] = (symbol, SORT_MAP[sort])

            sys_vars = [
                v
                for v in command.input_vars + command.output_vars + command.local_vars
                if v.sort in SORT_MAP
            ]
            for var in sys_vars:
                var.sort = SORT_MAP[var.sort]
                command.var_sorts[var.symbol] = var.sort

        context = Context()
        for term1 in command.get_terms():
            for term2 in postorder(term1, context):
                to_qfbv_term(term2)
