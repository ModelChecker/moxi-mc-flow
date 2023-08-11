"""
Representation of IL
"""
from __future__ import annotations
from enum import Enum
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

    def __eq__(self, __value: object) -> bool:
        """Two ILIdentifiers are equal if they have the same symbol and indices."""
        if not isinstance(__value, ILIdentifier):
            return False

        if self.symbol != __value.symbol:
            return False

        if len(self.indices) != len(__value.indices):
            return False 

        for i in range(0, len(self.indices)):
            if self.indices[i] != __value.indices[i]:
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
        self.sorts = sorts

    def arity(self) -> int:
        return len(self.sorts)

    def __eq__(self, __value: object) -> bool:
        if not isinstance(__value, ILSort):
            return False

        if is_bool_sort(self) and is_bv_sort(__value) and __value.identifier.indices[0] == 1:
            return True

        if is_bool_sort(__value) and is_bv_sort(self) and self.identifier.indices[0] == 1:
            return True

        if self.identifier != __value.identifier:
            return False

        return True
    
    def __hash__(self) -> int:
        if is_bool_sort(self):
            return hash(ILIdentifier("BitVec", [1]))
        return hash(self.identifier)
    
    def __str__(self) -> str:
        s = f"({self.identifier} "
        for sort in self.sorts:
            s += f"{sort} "
        return s[:-1]+")"


# Built-in sorts
IL_NO_SORT: ILSort = ILSort(ILIdentifier("", []), []) # placeholder sort
IL_BOOL_SORT: ILSort = ILSort(ILIdentifier("Bool", []), [])
IL_INT_SORT: ILSort = ILSort(ILIdentifier("Int", []), [])
IL_BITVEC_SORT: Callable[[int], ILSort] = lambda n: ILSort(ILIdentifier("BitVec", [n]), [])


def is_bool_sort(sort: ILSort) -> bool:
    if sort.identifier.symbol == "Bool" and len(sort.identifier.indices) == 0 and len(sort.sorts) == 0:
        return True
    return False


def is_bv_sort(sort: ILSort) -> bool:
    """A bit vector sort has an identifier with the symbol 'BitVec' and is indexed with a single numeral. Bool type is an implicit name for a bit vector of length one."""
    if len(sort.sorts) == 0 and ((sort.identifier.symbol == "BitVec" and len(sort.identifier.indices) == 1) or is_bool_sort(sort)):
        return True
    return False


def is_int_sort(sort: ILSort) -> bool:
    if sort.identifier.symbol == "Int" and len(sort.identifier.indices) == 0 and len(sort.sorts) == 0:
        return True
    return False


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
        self.scope: list[ILDefineSystem] = []

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


class ILApply(ILExpr):

    def __init__(self, sort: ILSort, identifier: ILIdentifier, children: list[ILExpr]):
        super().__init__(sort, children)
        self.identifier = identifier

    def __str__(self) -> str:
        s = f"({self.identifier} "
        for child in self.children:
            s += f"{child} "
        return s[:-1] + ")"


class ILSystem():
    
    def __init__(
        self, 
        input: list[ILVar], 
        state: list[ILVar],
        output: list[ILVar], 
        init: ILExpr,
        trans: ILExpr, 
        inv: ILExpr
    ):
        self.input = input
        self.state = state
        self.output = output
        self.init = init
        self.trans = trans
        self.inv = inv


class ILCommand():
    pass


class ILDeclareSort(ILCommand):

    def __init__(self, symbol: str, arity: int):
        super().__init__()
        self.symbol = symbol
        self.arity = arity


class ILDefineSort(ILCommand):

    def __init__(self, symbol: str, definition: ILSort):
        super().__init__()
        self.symbol = symbol
        self.definition = definition


class ILDeclareConst(ILCommand):

    def __init__(self, symbol: str, sort: ILSort):
        super().__init__()
        self.symbol = symbol
        self.sort = sort


class ILDefineSystem(ILCommand):
    
    def __init__(
        self, 
        symbol: str,
        input: dict[str, ILSort], 
        output: dict[str, ILSort], 
        local: dict[str, ILSort],
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

        # this gets populated by sort checker
        self.subsystems: dict[str, ILDefineSystem] = {}


class ILCheckSystem(ILCommand):
    
    def __init__(
        self, 
        sys_symbol: str,
        input: dict[str, ILSort], 
        output: dict[str, ILSort], 
        local: dict[str, ILSort],
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
        self.var_map: dict[str, str] = {}


class ILExit(ILCommand):
    pass


class ILLogic():

    def __init__(
        self, 
        name: str, 
        sort_symbols: dict[str, tuple[int, int]], 
        function_symbols: set[str],
        sort_check: Callable[[ILApply], bool]
    ):
        self.name = name
        self.sort_symbols = sort_symbols
        self.function_symbols = function_symbols
        self.sort_check = sort_check


def sort_check_apply_core(node: ILApply) -> bool:
    # "true", "false", "not", "=>", "and", "or", "xor", "=", "distinct", "ite"
    function = node.identifier

    if function.symbol == "true" or function.symbol == "false":
        # (true Bool)
        # (false Bool)
        if len(function.indices) != 0:
            return False

        if len(node.children) != 0:
            return False

        node.sort = IL_BOOL_SORT

        return True
    elif function.symbol == "not":
        # (not Bool Bool)
        if len(function.indices) != 0:
            return False

        if len(node.children) != 1:
            return False

        operand = node.children[0]

        if not is_bool_sort(operand.sort):
            return False

        node.sort = IL_BOOL_SORT

        return True
    elif function.symbol == "=>" or function.symbol == "and" or function.symbol == "or" or function.symbol == "xor":
        # (=> Bool Bool Bool)
        # (and Bool Bool Bool)
        # (or Bool Bool Bool)
        # (xor Bool Bool Bool)
        if len(function.indices) != 0:
            return False

        if len(node.children) != 2:
            return False

        (lhs,rhs) = node.children

        if not is_bool_sort(lhs.sort) or not is_bool_sort(rhs.sort):
            return False

        node.sort = IL_BOOL_SORT

        return True
    elif function.symbol == "=" or function.symbol == "distinct":
        # (par (A) (= A A Bool))
        # (par (A) (distinct A A Bool))
        if len(function.indices) != 0:
            return False

        if len(node.children) != 2:
            return False

        (lhs,rhs) = node.children

        if lhs.sort != rhs.sort:
            return False

        node.sort = IL_BOOL_SORT

        return True
    elif function.symbol == "=" or function.symbol == "distinct" or function.symbol == "!=":
        # (par (A) (ite Bool A A A))
        if len(function.indices) != 0:
            return False

        if len(node.children) != 3:
            return False

        (cond,if_,then_) = node.children

        if not is_bool_sort(cond.sort):
            return False

        if not if_.sort == then_.sort:
            return False

        node.sort = if_.sort

        return True
    
    return False


def sort_check_apply_bv(node: ILApply) -> bool:
    """Returns true if `node` corresponds to a valid function signature in SMT-LIB2 QF_BV logic."""
    function = node.identifier

    if function.symbol == "concat":
        # (concat (_ BitVec i) (_ BitVec j) (_ BitVec m))
        if len(function.indices) != 0:
            return False

        if len(node.children) != 2:
            return False

        (lhs, rhs) = node.children

        if not is_bv_sort(lhs.sort) or not is_bv_sort(rhs.sort):
            return False

        i = lhs.sort.identifier.indices[0]
        j = rhs.sort.identifier.indices[0]

        node.sort = IL_BITVEC_SORT(i+j)

        return True
    if function.symbol == "extract":
        # ((_ extract i j) (_ BitVec m) (_ BitVec n))
        if len(function.indices) != 2:
            return False
        
        (i,j) = function.indices

        if len(node.children) != 1:
            return False

        operand = node.children[0]

        if not is_bv_sort(operand.sort):
            return False

        m = operand.sort.identifier.indices[0]
        if not i <= m and j <= i:
            return False

        node.sort = IL_BITVEC_SORT(i-j+1)

        return True
    elif function.symbol == "bvnot":
        # (bvnot (_ BitVec m) (_ BitVec m))
        if len(function.indices) != 0:
            return False
        
        if len(node.children) != 1:
            return False

        operand = node.children[0]

        if not is_bv_sort(operand.sort):
            return False

        m = operand.sort.identifier.indices[0]
        node.sort = IL_BITVEC_SORT(m)

        return True
    elif function.symbol == "bvand" or function.symbol == "bvadd" or function.symbol == "bvsmod":
        # (bvand (_ BitVec m) (_ BitVec m) (_ BitVec m))
        if len(function.indices) != 0:
            return False
        
        if len(node.children) != 2 or not is_bv_sort(node.children[0].sort) or not is_bv_sort(node.children[1].sort):
            return False

        m = node.children[0].sort.identifier.indices[0]
        node.sort = IL_BITVEC_SORT(m)

        return True

    return False


FUNCTIONS_CORE = {"true", "false", "not", "=>", "and", "or", "xor", "=", "distinct", "ite"}

# TODOs are for implementing in sort checker
FUNCTIONS_BV = {
   "concat",
   "extract",
   "zero_extend", # TODO
   "sign_extend", # TODO
   "rotate_left", # TODO
   "rotate_right", # TODO
   "bvshl", # TODO
   "bvlshr", # TODO
   "bvashr", # TODO
   "bvnot",
   "bvneg", # TODO
   "bvand",
   "bvnand", # TODO
   "bvor", # TODO
   "bvnor", # TODO
   "bvxor", # TODO
   "bvxnor", # TODO
   "bvadd", 
   "bvsub", # TODO
   "bvmul", # TODO
   "bvudiv", # TODO
   "bvsdiv", # TODO
   "bvurem", # TODO
   "bvsrem", # TODO
   "bvsmod",
   "bvult", # TODO
   "bvule", # TODO
   "bvugt", # TODO
   "bvuge", # TODO
   "bvslt", # TODO
   "bvsle", # TODO
   "bvsgt", # TODO
   "bvsge", # TODO
   "reduce_and", # TODO
   "reduce_or", # TODO
   "reduce_xor" # TODO
}

QF_BV = ILLogic("QF_BV", {"BitVec": (1,0)}, FUNCTIONS_BV, sort_check_apply_bv)

FuncSig = tuple[list[ILSort], ILSort]


class ILContext():

    def __init__(self):
        self.declared_sorts: dict[ILIdentifier, int] = {}
        self.defined_sorts: set[ILSort] = set()
        self.declared_functions: dict[str, FuncSig] = {}
        self.defined_functions: dict[str, tuple[FuncSig, ILExpr]] = {}
        self.defined_systems: dict[str, ILDefineSystem] = {}
        self.logic = QF_BV # for now, assume QF_BV logic
        self.input_vars: dict[str, ILSort] = {}
        self.output_vars: dict[str, ILSort] = {}
        self.local_vars: dict[str, ILSort] = {}
        self.system_symbol_stack: list[str] = [] # used during system flattening

    def get_symbols(self) -> set[str]:
        symbols = set()

        symbols.update([id.symbol for id in self.declared_sorts])
        symbols.update([srt.identifier.symbol for srt in self.defined_sorts])
        symbols.update([sym for sym in self.declared_functions])
        symbols.update([sym for sym in self.defined_functions])
        symbols.update([sym for sym in self.defined_systems])

        return symbols


class ILProgram():

    def __init__(self, commands: list[ILCommand]):
        self.commands: list[ILCommand] = commands

    def get_check_system_cmds(self) -> list[ILCheckSystem]:
        return [cmd for cmd in self.commands if isinstance(cmd, ILCheckSystem)]


def postorder_iterative(expr: ILExpr, func: Callable[[ILExpr], Any]):
    """Perform an iterative postorder traversal of `expr`, calling `func` on each node."""
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
        """Return true if node is well-sorted where `no_prime` is true if primed variables are disabled and `prime_input` is true if input variable are allowed to be primed (true for check-system assumptions and reachability conditions). """
        nonlocal context

        if isinstance(node, ILConstant):
            return True
        elif isinstance(node, ILVar) and node.symbol in context.input_vars:
            node.var_type = ILVarType.INPUT
            node.sort = context.input_vars[node.symbol]

            if node.prime and not prime_input:
                print(f"Error: primed input variables only allowed in check system assumptions and reachability conditions ({node.symbol}).")
                return False

            return True
        elif isinstance(node, ILVar) and node.symbol in context.output_vars:
            node.var_type = ILVarType.OUTPUT
            node.sort = context.output_vars[node.symbol]

            if node.prime and no_prime:
                print(f"Error: primed variables only allowed in system transition relation ({node.symbol}).")
                return False

            return True
        elif isinstance(node, ILVar) and node.symbol in context.local_vars:
            node.var_type = ILVarType.LOCAL
            node.sort = context.local_vars[node.symbol]

            if node.prime and no_prime:
                print(f"Error: primed variables only allowed in system transition relation ({node.symbol}).")
                return False

            return True
        elif isinstance(node, ILApply):
            arg_sorts: list[ILSort] = []
            return_sort: ILSort = IL_NO_SORT

            if node.identifier.symbol in FUNCTIONS_CORE:
                for arg in node.children:
                    sort_check_expr(arg, no_prime, prime_input)

                if not sort_check_apply_core(node):
                    print(f"Error: function signature does not match definition ({node}).")
                    return False
                return True
            if node.identifier.symbol in context.logic.function_symbols:
                for arg in node.children:
                    sort_check_expr(arg, no_prime, prime_input)

                if not context.logic.sort_check(node):
                    print(f"Error: function signature does not match definition ({node}).")
                    return False
                return True
            elif node.identifier.symbol in context.defined_functions:
                ((arg_sorts, return_sort), expr) = context.defined_functions[node.identifier.symbol]

                if len(arg_sorts) != len(node.children):
                    print(f"Error: function args do not match definition ({node}).")
                    return False

                for i in range(0, len(arg_sorts)):
                    sort_check_expr(node.children[i], no_prime, prime_input)
                    if arg_sorts[i] != node.children[i].sort:
                        print(f"Error: function args do not match definition ({node}).")
                        return False
            else:
                print(f"Error: symbol `{node.identifier.symbol}` not recognized.")
                return False

            node.sort = return_sort
            return True

        print(f"Error: node type `{node.__class__}` not recognized ({node}).")
        return False
    # end sort_check_expr

    for cmd in program.commands:
        if isinstance(cmd, ILDeclareSort):
            if cmd.symbol in context.get_symbols():
                print(f"Error: symbol `{cmd.symbol}` already in use.")
                status = False

            # TODO
        elif isinstance(cmd, ILDefineSort):
            if cmd.symbol in context.get_symbols():
                print(f"Error: symbol `{cmd.symbol}` already in use.")
                status = False

            # TODO
        elif isinstance(cmd, ILDeclareConst):
            if cmd.symbol in context.get_symbols():
                print(f"Error: symbol `{cmd.symbol}` already in use.")
                status = False

            context.declared_functions[cmd.symbol] = FuncSig(([], cmd.sort))
        elif isinstance(cmd, ILDefineSystem):
            # TODO: check for variable name clashes across cmd.input, cmd.output, cmd.local
            context.input_vars = cmd.input
            context.output_vars = cmd.output
            context.local_vars = cmd.local

            status = status and sort_check_expr(cmd.init, True, False)
            status = status and sort_check_expr(cmd.trans, False, False)
            status = status and sort_check_expr(cmd.inv, True, False)

            for name,subsystem in cmd.subsystem_signatures.items():
                # TODO: check for cycles in system dependency graph
                (sys_symbol, signature) = subsystem

                if sys_symbol not in context.defined_systems:
                    print(f"Error: system `{sys_symbol}` not defined in context.")
                    status = False

                target_system = context.defined_systems[sys_symbol]
                target_signature = target_system.input | target_system.output

                if len(signature) != len(target_signature):
                    print(f"Error: subsystem signature does not match target system ({sys_symbol}).\n\t{context.defined_systems[sys_symbol].input | context.defined_systems[sys_symbol].output}\n\t{signature}")
                    status = False
                    continue

                cmd_variables = cmd.input | cmd.output | cmd.local
                for var_symbol, sort in zip(signature, target_signature.values()):
                    if var_symbol not in cmd_variables:
                        print(f"Error: variable `{var_symbol}` not declared.")
                        status = False
                        continue
                    elif cmd_variables[var_symbol] != sort:
                        print(f"Error: subsystem signature does not match target system ({sys_symbol}).\n\t{context.defined_systems[sys_symbol].input | context.defined_systems[sys_symbol].output}\n\t{signature}")
                        status = False
                        continue

                cmd.subsystems[name] = context.defined_systems[sys_symbol]

            context.defined_systems[cmd.symbol] = cmd

            context.input_vars = {}
            context.output_vars = {}
            context.local_vars = {}
        elif isinstance(cmd, ILCheckSystem):
            if not cmd.sys_symbol in context.defined_systems:
                print(f"Error: system `{cmd.sys_symbol}` undefined.")
                status = False
                continue

            context.input_vars = cmd.input
            context.output_vars = cmd.output
            context.local_vars = cmd.local

            system = context.defined_systems[cmd.sys_symbol]

            if len(system.input) != len(cmd.input):
                print(f"Error: input variables do not match target system ({system.symbol}).\n\t{system.input}\n\t{cmd.input}")
                status = False
                continue

            for (v1,s1),(v2,s2) in zip(system.input.items(), cmd.input.items()):
                if s1 != s2:
                    print(f"Error: sorts do not match in check-system (expected {s1}, got {s2})")
                    status = False
                    continue
                cmd.var_map[v1] = v2

            if len(system.output) != len(cmd.output):
                print(f"Error: output variables do not match target system ({system.symbol}).\n\t{system.output}\n\t{cmd.output}")
                status = False
                continue

            for (v1,s1),(v2,s2) in zip(system.output.items(), cmd.output.items()):
                if s1 != s2:
                    print(f"Error: sorts do not match in check-system (expected {s1}, got {s2})")
                    status = False
                    continue
                cmd.var_map[v1] = v2

            if len(system.local) != len(cmd.local):
                print(f"Error: local variables do not match target system ({system.symbol}).\n\t{system.input}\n\t{cmd.input}")
                status = False
                continue

            for (v1,s1),(v2,s2) in zip(system.local.items(), cmd.local.items()):
                if s1 != s2:
                    print(f"Error: sorts do not match in check-system (expected {s1}, got {s2})")
                    status = False
                    continue
                cmd.var_map[v1] = v2

            for expr in cmd.assumption.values():
                status = status and sort_check_expr(expr, False, True)

            for expr in cmd.reachable.values():
                status = status and sort_check_expr(expr, False, True)

            for expr in cmd.fairness.values():
                status = status and sort_check_expr(expr, False, True)

            for expr in cmd.current.values():
                status = status and sort_check_expr(expr, False, True)

            context.input_vars = {}
            context.output_vars = {}
            context.local_vars = {}
        else:
            raise NotImplementedError

    return (status, context)