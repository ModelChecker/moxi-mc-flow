from __future__ import annotations
from typing import Any, Callable, NewType

from numpy import intp

from btor2 import *


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
        return isinstance(__value, ILSort) and self.identifier == __value.identifier
    
    def __hash__(self) -> int:
        return hash(self.identifier)
    
    def __str__(self) -> str:
        s = f"({self.identifier} "
        for sort in self.sorts:
            s += f"{sort} "
        return s[:-1]+")"


# Built-in sorts
IL_NO_SORT: ILSort = ILSort(ILIdentifier("", []), []) # placeholder sort
IL_BOOL_SORT: ILSort = ILSort(ILIdentifier("Bool", []), [])
IL_BITVEC_SORT: Callable[[int], ILSort] = lambda n: ILSort(ILIdentifier("BitVec", [n]), [])


def is_bv_sort(sort: ILSort) -> bool:
    """A bit vector sort has an identifier with the symbol 'BitVec' and is indexed with a single numeral."""
    if sort.identifier.symbol != "BitVec" or len(sort.sorts) != 0 or len(sort.identifier.indices) != 1:
        return False
    return True


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


class ILVar(ILExpr):
    """An ILVar requires a sort and symbol."""

    def __init__(self, sort: ILSort, symbol: str):
        super().__init__(sort, [])
        self.symbol = symbol

    def __eq__(self, __value: object) -> bool:
        """Two ILVars are equal if they have the same symbol."""
        if isinstance(__value, ILVar):
            return self.symbol == __value.symbol
        return False

    def __hash__(self) -> int:
        return hash(self.symbol)

    def __str__(self) -> str:
        return f"{self.symbol}"


class ILInputVar(ILVar):

    def __init__(self, sort: ILSort, symbol: str):
        super().__init__(sort, symbol)


class ILOutputVar(ILVar):

    def __init__(self, sort: ILSort, symbol: str, prime: bool):
        super().__init__(sort, symbol)
        self.prime = prime

    def __str__(self) -> str:
        return super().__str__() + ("'" if self.prime else "")


class ILLocalVar(ILVar):

    def __init__(self, sort: ILSort, symbol: str, prime: bool):
        super().__init__(sort, symbol)
        self.prime = prime

    def __str__(self) -> str:
        return super().__str__() + ("'" if self.prime else "")


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

    def __init__(self, identifier: str, arity: int):
        super().__init__()
        self.identifier = identifier
        self.arity = arity


class ILDefineSort(ILCommand):

    def __init__(self, identifier: str, definition: ILSort):
        super().__init__()
        self.identifier = identifier
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
        local: dict[str, ILSort],
        output: dict[str, ILSort], 
        init: ILExpr,
        trans: ILExpr, 
        inv: ILExpr
    ):
        self.symbol = symbol
        self.input = input
        self.local = local
        self.output = output
        self.init = init
        self.trans = trans
        self.inv = inv


class ILCheckSystem(ILCommand):
    
    def __init__(
        self, 
        system: str,
        input: dict[str, ILSort], 
        local: dict[str, ILSort],
        output: dict[str, ILSort], 
        assumption: dict[str, ILExpr],
        fairness: dict[str, ILExpr], 
        reachable: dict[str, ILExpr], 
        current: dict[str, ILExpr], 
        query: dict[str, list[str]], 
    ):
        self.system = system
        self.input = input
        self.output = output
        self.local = local
        self.assumption = assumption
        self.fairness = fairness
        self.reachable = reachable
        self.current = current
        self.query = query


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


def sort_check_apply_bv(node: ILApply) -> bool:
    """True if node corresponds to function signature in SMT-LIB2 QF_BV logic."""
    function = node.identifier

    if function.symbol == "=":
        # (= (_ BitVec m) (_ BitVec m) Bool)
        if len(function.indices) != 0:
            return False

        if len(node.children) != 2:
            return False

        if not is_bv_sort(node.children[0].sort) or not is_bv_sort(node.children[1].sort):
            return False

        m = node.children[0].sort.identifier.indices[0]
        if m != node.children[1].sort.identifier.indices[0]:
            return False

        node.sort = IL_BOOL_SORT

        return True
    elif function.symbol == "extract":
        # ((_ extract i j) (_ BitVec m) (_ BitVec n))
        if len(function.indices) != 2:
            return False
        
        i,j = function.indices[0], function.indices[1]

        if len(node.children) != 1 or not is_bv_sort(node.children[0].sort):
            return False

        m = node.children[0].sort.identifier.indices[0]
        if not i <= m and j <= i:
            return False

        node.sort = IL_BITVEC_SORT(i-j+1)

        return True
    elif function.symbol == "bvnot":
        # (bvnot (_ BitVec m) (_ BitVec m))
        if len(function.indices) != 0:
            return False
        
        if len(node.children) != 1 or not is_bv_sort(node.children[0].sort):
            return False

        m = node.children[0].sort.identifier.indices[0]
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


FUNCTIONS_BV = {"=", "extract", "bvnot", "bvand", "bvadd", "bvsmod"}
QF_BV = ILLogic("QF_BV", {"BitVec": (1,0)}, FUNCTIONS_BV, sort_check_apply_bv)

FuncSig = NewType("FuncSig", tuple[list[ILSort], ILSort])


class ILContext():

    def __init__(self):
        self.declared_sorts: dict[ILIdentifier, int] = {}
        self.defined_sorts: set[ILSort] = set()
        self.declared_functions: dict[str, FuncSig] = {}
        self.defined_functions: dict[str, tuple[FuncSig, ILExpr]] = {}
        self.defined_systems: dict[str, ILSystem] = {}
        self.logic = QF_BV # for now, assume QF_BV logic
        self.system_context: list[ILDefineSystem] = [] # context stack of systems
        self.input_vars: dict[str, ILSort] = {}
        self.output_vars: dict[str, ILSort] = {}
        self.local_vars: dict[str, ILSort] = {}


class ILProgram():

    def __init__(self, commands: list[ILCommand]):
        self.commands: list[ILCommand] = commands


def postorder_iterative(expr: ILExpr, func: Callable[[ILExpr], Any]):
    """Perform an iterative postorder traversal of `expr`, calling `func` on each node."""
    stack: list[tuple[bool, ILExpr]] = []
    visited: set[int] = set()

    stack.append((False, expr))

    while len(stack) > 0:
        cur = stack.pop()

        if cur[0]:
            func(cur[1])
            continue
        elif id(cur[1]) in visited:
            continue

        visited.add(id(cur[1]))
        stack.append((True, cur[1]))
        for child in cur[1].children:
            stack.append((False, child))


def sort_check(program: ILProgram) -> bool:
    context: ILContext = ILContext()
    status: bool = True

    def sort_check_expr(node: ILExpr, no_prime: bool) -> bool:
        nonlocal context

        if isinstance(node, ILInputVar):
            return True
        if isinstance(node, ILOutputVar) or isinstance(node, ILLocalVar):
            if node.prime and no_prime:
                print(f"Error: primed variables only allowed in system transition relation ({node.symbol}).")
                return False
            return True
        elif isinstance(node, ILApply):
            arg_sorts: list[ILSort] = []
            return_sort: ILSort = IL_NO_SORT

            if node.identifier.symbol in context.logic.function_symbols:
                for arg in node.children:
                    sort_check_expr(arg, no_prime)
                return context.logic.sort_check(node)
            elif node.identifier.symbol in context.defined_functions:
                ((arg_sorts, return_sort), expr) = context.defined_functions[node.identifier.symbol]

                if len(arg_sorts) != len(node.children):
                    return False

                for i in range(0, len(arg_sorts)):
                    sort_check_expr(node.children[i], no_prime)
                    if arg_sorts[i] != node.children[i].sort:
                        return False
            else:
                return False

            node.sort = return_sort
            return True

        return False
    # end sort_check_expr

    for cmd in program.commands:
        if isinstance(cmd, ILDeclareSort):
            pass
        elif isinstance(cmd, ILDefineSort):
            pass
        elif isinstance(cmd, ILDeclareConst):
            context.declared_functions[cmd.symbol] = FuncSig(([], cmd.sort))
        elif isinstance(cmd, ILDefineSystem):
            # TODO: check for variable name clashes across cmd.input, cmd.output, cmd.local
            context.system_context.append(cmd)

            sort_check_expr(cmd.init, True)
            sort_check_expr(cmd.trans, False)
            sort_check_expr(cmd.inv, True)
        elif isinstance(cmd, ILCheckSystem):
            if not cmd.system in [sys.symbol for sys in context.system_context]:
                print(f"Error: system `{cmd.system}` undefined.")

            
        else:
            raise NotImplementedError

    return status