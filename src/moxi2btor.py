from copy import copy
import json
from pathlib import Path
import pickle
from typing import cast, Optional

from src import json2moxi, log, btor, moxi, parse_moxi

FILE_NAME = Path(__file__).name

moxi_fun_map: dict[str, btor.BtorOperator] = {
    "=": btor.BtorOperator.EQ,
    "distinct": btor.BtorOperator.NEQ,
    "=>": btor.BtorOperator.IMPLIES,
    "iff": btor.BtorOperator.IFF,
    "not": btor.BtorOperator.NOT,
    "and": btor.BtorOperator.AND,
    "or": btor.BtorOperator.OR,
    "xor": btor.BtorOperator.XOR,
    "ite": btor.BtorOperator.ITE,
    "concat": btor.BtorOperator.CONCAT,
    "extract": btor.BtorOperator.SLICE,
    "zero_extend": btor.BtorOperator.UEXT,
    "sign_extend": btor.BtorOperator.SEXT,
    "rotate_left": btor.BtorOperator.ROL,
    "rotate_right": btor.BtorOperator.ROR,
    "bvshl": btor.BtorOperator.SLL,
    "bvlshr": btor.BtorOperator.SRL,
    "bvashr": btor.BtorOperator.SRA,
    "bvnot": btor.BtorOperator.NOT,
    "bvneg": btor.BtorOperator.NEG,
    "bvand": btor.BtorOperator.AND,
    "bvnand": btor.BtorOperator.NAND,
    "bvor": btor.BtorOperator.OR,
    "bvnor": btor.BtorOperator.NOR,
    "bvxor": btor.BtorOperator.XOR,
    "bvxnor": btor.BtorOperator.XNOR,
    "bvadd": btor.BtorOperator.ADD,
    "bvsub": btor.BtorOperator.SUB,
    "bvmul": btor.BtorOperator.MUL,
    "bvudiv": btor.BtorOperator.UDIV,
    "bvsdiv": btor.BtorOperator.SDIV,
    "bvurem": btor.BtorOperator.UREM,
    "bvsrem": btor.BtorOperator.SREM,
    "bvsmod": btor.BtorOperator.SMOD,
    "bvult": btor.BtorOperator.ULT,
    "bvule": btor.BtorOperator.ULTE,
    "bvugt": btor.BtorOperator.UGT,
    "bvuge": btor.BtorOperator.UGTE,
    "bvslt": btor.BtorOperator.SLT,
    "bvsle": btor.BtorOperator.SLTE,
    "bvsgt": btor.BtorOperator.SGT,
    "bvsge": btor.BtorOperator.SGTE,
    "reduce_and": btor.BtorOperator.REDAND,
    "reduce_or": btor.BtorOperator.REDOR,
    "reduce_xor": btor.BtorOperator.REDXOR,
    "select": btor.BtorOperator.READ,
    "store": btor.BtorOperator.WRITE,
}

# A SortMap maps moxi.Sorts to BTOR2 sorts
SortMap = dict[moxi.Sort, btor.BtorSort]

# An ExprMap maps moxi.Exprs to btor.BtorExprs
ExprMap = dict[moxi.Term, btor.BtorExpr]

BtorVarType = tuple[
    Optional[btor.BtorStateVar], btor.BtorStateVar, Optional[btor.BtorStateVar]
]

# A VarMap maps variables in a system context to BTOR2 variables. BTOR2 variables are tuples by
# default (to handle initial, current, and next values) for output and state variables, whereas
# inputs are just a single variable.
VarMap = dict[tuple[str, moxi.SystemContext], BtorVarType]


def get_const_vars(context: moxi.Context, var_map: VarMap):
    return {
        btor_cur
        for (moxi_var_symbol, _), (_, btor_cur, _) in var_map.items()
        if btor_cur and moxi_var_symbol in context.declared_consts.keys()
    }


def moxisort2btorsort(
    sort: moxi.Sort, context: moxi.Context, sort_map: SortMap
) -> btor.BtorSort:
    if sort in sort_map:
        btor2_sort = sort_map[sort]
    elif moxi.is_bool_sort(sort):
        btor2_sort = btor.BtorBitVec(1)
    elif moxi.is_bitvec_sort(sort):
        btor2_sort = btor.BtorBitVec(sort.identifier.indices[0])
    elif moxi.is_array_sort(sort):
        btor2_sort = btor.BtorArray(
            moxisort2btorsort(sort.parameters[0], context, sort_map),
            moxisort2btorsort(sort.parameters[1], context, sort_map),
        )
    elif sort.identifier.symbol in context.declared_enum_sorts:
        width = len(context.declared_enum_sorts[sort.identifier.symbol]).bit_length()
        btor2_sort = btor.BtorBitVec(width)
    else:
        raise NotImplementedError(f"moxi. sort '{sort}' ({type(sort)}) unrecognized")

    if sort not in sort_map:
        sort_map[sort] = btor2_sort

    return btor2_sort


def build_sort_map_expr(
    node: moxi.Term, context: moxi.Context, sort_map: SortMap
) -> SortMap:
    """Iteratively recurse `node` and map each `moxi.Sort` to a `btor.BtorSort`."""
    for expr in moxi.postorder(node, context):
        if expr.sort not in sort_map:
            moxisort2btorsort(expr.sort, context, sort_map)

    return sort_map


def build_sort_map_cmd(
    cmd: moxi.Command, context: moxi.Context, sort_map: SortMap
) -> SortMap:
    if isinstance(cmd, moxi.DefineSystem):
        for subsystem in cmd.subsystems.values():
            build_sort_map_cmd(subsystem, context, sort_map)
        for expr in cmd.get_terms():
            build_sort_map_expr(expr, context, sort_map)
    elif isinstance(cmd, moxi.CheckSystem):
        for expr in cmd.get_terms():
            build_sort_map_expr(expr, context, sort_map)
    else:
        raise NotImplementedError

    return sort_map


def build_var_map_expr(
    node: moxi.Term, context: moxi.Context, sort_map: SortMap, var_map: VarMap
) -> None:
    """Iteratively recurse `node` and map each `(moxi.Var, moxi.SystemContext)` pair to a `BtorVarType`. Assumes that the sort of every sub-expression in `node` is present in `sort_map`."""
    for expr in moxi.postorder(node, context):
        if (
            not isinstance(expr, moxi.Variable)
            or (expr.symbol, context.system_context) in var_map
        ):
            continue

        var, system_context = context.lookup_var(expr.symbol, context.system_context)

        symbol = moxi.get_scoped_var_symbol(var, system_context)

        # note: those system context copies only copy the pointers + they are only as big as the subsystems are deep
        if var in system_context.get_input_symbols():
            var_map[(expr.symbol, context.system_context.copy())] = (
                None,
                btor.BtorStateVar(
                    sort_map[system_context.get_sort(var)], f"{symbol}.cur"
                ),
                btor.BtorStateVar(
                    sort_map[system_context.get_sort(var)], f"{symbol}.next"
                ),
            )
        elif (
            var in system_context.get_output_symbols()
            or var in system_context.get_local_symbols()
        ):
            var_map[(expr.symbol, context.system_context.copy())] = (
                btor.BtorStateVar(
                    sort_map[system_context.get_sort(var)], f"{symbol}.init"
                ),
                btor.BtorStateVar(
                    sort_map[system_context.get_sort(var)], f"{symbol}.cur"
                ),
                btor.BtorStateVar(
                    sort_map[system_context.get_sort(var)], f"{symbol}.next"
                ),
            )
        elif expr.symbol in context.declared_consts:
            var_map[(expr.symbol, context.system_context.copy())] = (
                None,
                btor.BtorStateVar(sort_map[expr.sort], f"{symbol}.cur"),
                None,
            )
        # else var is a bound variable, skip


def build_var_map_cmd(
    cmd: moxi.Command, context: moxi.Context, sort_map: SortMap, var_map: VarMap
) -> None:
    """Update `var_map` to map all `moxi.Var` instances to `btor.BtorVar`s"""
    if isinstance(cmd, moxi.CheckSystem):
        context.push_system(cmd.symbol, cmd, [])

        target_system = context.defined_systems[cmd.symbol]
        context.push_system(cmd.symbol, target_system, cmd.full_signature)

        build_var_map_cmd(target_system, context, sort_map, var_map)

        context.pop_system()

        for expr in cmd.get_terms():
            build_var_map_expr(expr, context, sort_map, var_map)

        context.pop_system()
    elif isinstance(cmd, moxi.DefineSystem):
        for subsys_symbol, subsystem in cmd.subsystems.items():
            context.push_system(
                subsys_symbol, subsystem, cmd.get_subsys_params(subsys_symbol)
            )

            build_var_map_cmd(subsystem, context, sort_map, var_map)

            context.pop_system()

        for expr in cmd.get_terms():
            build_var_map_expr(expr, context, sort_map, var_map)
    else:
        raise NotImplementedError


def build_expr_map(
    node: moxi.Term,
    context: moxi.Context,
    is_init_expr: bool,
    sort_map: SortMap,
    var_map: VarMap,
    expr_map: ExprMap,
) -> None:
    """Builds `expr_map` by mapping each sub-expression of `node` to an equivalent `btor.BtorExpr`. Assumes that the sort of every sub-expression in `node` is present in `sort_map` and every `(moxi.Var, moxi.SystemContext)` pair is present in `var_map`."""
    for expr in moxi.postorder(node, context):
        if isinstance(expr, moxi.Variable) and expr.symbol in context.bound_let_vars:
            expr_map[expr] = expr_map[context.bound_let_vars[expr.symbol]]
        elif isinstance(expr, moxi.Variable) and all(
            [b for b in var_map[(expr.symbol, context.system_context)]]
        ):
            # We use "int(not is_init_expr) + int(expr.prime)" to compute the index in var_map tuple:
            #   var_map[var] = (init, cur, next)
            idx = int(not is_init_expr) + int(expr.prime)
            btor_var = var_map[(expr.symbol, context.system_context)][idx]

            if not btor_var:
                symbol = "::".join(
                    context.system_context.get_scope_symbols() + [expr.symbol]
                )
                raise ValueError(f"No BTOR2 var for {symbol}")

            expr_map[expr] = btor_var
        elif isinstance(expr, moxi.Variable):
            # We use "int(expr.prime)" to compute the index in var_map tuple:
            #   var_map[var] = (init, cur, next)
            idx = 1 + int(expr.prime)
            btor_var = var_map[(expr.symbol, context.system_context)][idx]

            if not btor_var:
                symbol = "::".join(
                    context.system_context.get_scope_symbols() + [expr.symbol]
                )
                raise ValueError(f"No BTOR2 var for {symbol}")

            expr_map[expr] = btor_var
        elif (
            isinstance(expr, moxi.Constant)
            and expr.sort.identifier.symbol in context.declared_enum_sorts
        ):
            value = context.declared_enum_sorts[expr.sort.identifier.symbol].index(
                expr.value
            )
            expr_map[expr] = btor.BtorConst(sort_map[expr.sort], value)
        elif isinstance(expr, moxi.Constant):
            expr_map[expr] = btor.BtorConst(sort_map[expr.sort], expr.value)
        elif moxi.is_const_array_expr(expr):
            pass
        elif isinstance(expr, moxi.Apply) and expr.identifier.symbol in moxi_fun_map:
            if len(expr.children) > 3:
                raise NotImplementedError(
                    f"Unsupported expression '{expr}' (too many arguments)"
                )

            # pad indices with None
            tmp_indices = copy(expr.identifier.indices) + (
                [None] * (2 - len(expr.identifier.indices))
            )
            (idx1, idx2) = tuple(tmp_indices)

            # pad children with None
            tmp_children = copy(expr.children) + ([None] * (3 - len(expr.children)))
            (arg1, arg2, arg3) = tuple(tmp_children)

            btor2_args = (
                expr_map[arg1] if arg1 else None,
                expr_map[arg2] if arg2 else None,
                expr_map[arg3] if arg3 else None,
            )

            expr_map[expr] = btor.BtorApply(
                sort_map[expr.sort],
                moxi_fun_map[expr.identifier.symbol],
                (idx1, idx2),
                btor2_args,
            )
        elif isinstance(expr, moxi.LetTerm):
            expr_map[expr] = expr_map[expr.get_term()]
        else:
            raise NotImplementedError(f"Unsupported expression '{expr}'")


def to_btor2_constraint(
    expr: moxi.Term,
    context: moxi.Context,
    is_init_expr: bool,
    sort_map: SortMap,
    var_map: VarMap,
    expr_map: ExprMap,
    comment: str = "",
) -> list[btor.BtorNode]:
    """Returns a list of `btor.BtorNode`s generated by translating `expr` and adding the result as a constraint. If `is_init_expr` is true, uses initial variants of variables. Sets `comment` as the comment of the constraint node."""
    btor2_nodes: list[btor.BtorNode] = []

    build_expr_map(expr, context, is_init_expr, sort_map, var_map, expr_map)
    btor2_nodes += btor.flatten_btor2_expr(expr_map[expr])
    btor2_constraint = btor.BtorConstraint(expr_map[expr])
    btor2_nodes.append(btor2_constraint)
    btor2_constraint.set_comment(comment)

    return btor2_nodes


def to_btor2_define_system(
    system: moxi.DefineSystem,
    context: moxi.Context,
    sort_map: SortMap,
    var_map: VarMap,
    expr_map: ExprMap,
) -> list[btor.BtorNode]:
    """Returns a list of `btor.BtorNode`s generated by translating `system`. Asserts the various init, trans, and inv expressions as constraints."""
    btor2_nodes: list[btor.BtorNode] = []

    for symbol, subsystem in system.subsystems.items():
        context.push_system(symbol, subsystem, system.get_subsys_params(symbol))
        btor2_nodes += to_btor2_define_system(
            subsystem, context, sort_map, var_map, expr_map
        )
        context.pop_system()

    system_symbol = "::".join(context.system_context.get_scope_symbols())

    btor2_nodes += to_btor2_constraint(
        system.init, context, True, sort_map, var_map, expr_map, f"init {system_symbol}"
    )
    btor2_nodes += to_btor2_constraint(
        system.trans,
        context,
        False,
        sort_map,
        var_map,
        expr_map,
        f"trans {system_symbol}",
    )
    btor2_nodes += to_btor2_constraint(
        system.inv, context, False, sort_map, var_map, expr_map, f"inv {system_symbol}"
    )

    return btor2_nodes


def to_btor2_annotations(
    check: moxi.CheckSystem,
    context: moxi.Context,
    var_map: VarMap,
) -> list[btor.BtorNode]:
    """Returns a list of `btor.BtorNode`s that define annotations for a BTOR2 program that are necessary for the translation of BTOR2 witnesses to moxi. witnesses.

    1. Annotates enumeration-sorted variables with an `E` and the list of their potential values.
    2. Annotates array-sorted variables with an `A`and their index/element sorts.
    3. Annotates input variables with an `I`, since moxi. allows for primed inputs in certain spots (i.e., we can't use `btor.BtorInputVar`s in our translation). Only variables of `check` can be inputs.
    4. Annotates Boolean variables with a `B`, moxi. since distinguishes between Booleans and bit vectors of length 1 and BTOR2 does not.
    """
    btor2_annotations: list[btor.BtorNode] = []
    handled: set[tuple[str,str]] = set()
    const_vars = get_const_vars(context, var_map)

    for var_symbol, sys_ctx, cur in [
        (var_symbol, sys_ctx, cur)
        for (var_symbol, sys_ctx), (_, cur, _) in var_map.items()
    ]:
        top = sys_ctx.get_top()
        if not top:
            raise ValueError(f"System context for {var_symbol} is empty")
        (_, system) = top
        
        # Note: var_map may have repeat values (i.e., renamed variables point to
        # same btor.Btor variables)
        if (var_symbol, system.symbol) in handled:
            continue
        handled.add((var_symbol, system.symbol))

        sort = system.get_sort(var_symbol)
        if not sort and cur in const_vars:
            sort = context.declared_consts[var_symbol]
        elif not sort:
            raise ValueError(f"Variable {var_symbol} does not exist in context")

        # Add enum encoding information
        if sort.symbol in context.declared_enum_sorts:
            enum_sort_symbols = context.declared_enum_sorts[sort.symbol]
            enum_encoding = (
                f"E {cur.with_no_suffix()} = " f"{' '.join(enum_sort_symbols)}"
            )

            enum_var_comment = btor.BtorNode()
            enum_var_comment.set_comment_no_space(enum_encoding)
            btor2_annotations.append(enum_var_comment)

        # Add array sorts
        # Note that solvers only support bitvec -> bitvec arrays
        if moxi.is_array_sort(sort):
            index_sort = sort.parameters[0]
            element_sort = sort.parameters[1]
            if moxi.is_array_sort(index_sort) or moxi.is_array_sort(element_sort):
                log.error(
                    "Warning: BTOR2 solvers only support arrays of sort signature (Array (_ BitVec X) (_ BitVec Y)). Not adding sort annotation to BTOR2 file.",
                    FILE_NAME,
                )
                continue

            index_sort_width = index_sort.get_index(0)
            element_sort_width = element_sort.get_index(0)
            sort_encoding = (
                f"A {cur.with_no_suffix()} = "
                f"{index_sort_width} {element_sort_width}"
            )

            sort_comment = btor.BtorNode()
            sort_comment.set_comment_no_space(sort_encoding)
            btor2_annotations.append(sort_comment)

        # Add Bool var symbols. moxi. distinguishes between Bool and bit vectors of
        # length 1, BTOR2 does not.
        if moxi.is_bool_sort(sort):
            bool_encoding = f"B {cur.with_no_suffix()}"
            sort_comment = btor.BtorNode()
            sort_comment.set_comment_no_space(bool_encoding)
            btor2_annotations.append(sort_comment)

        # Add input var symbols. moxi. allows for primed inputs in certain spots,
        # so we can't use btor.BtorInputVar in our translation. Only use vars in
        # `check`, all others are mapped to other vars or are locals.
        top_level_system = sys_ctx.get_bottom()
        if (
            var_symbol in check.input_symbols
            and top_level_system
            and top_level_system[0] == system.symbol
        ):
            bool_encoding = f"I {cur.with_no_suffix()}"
            sort_comment = btor.BtorNode()
            sort_comment.set_comment_no_space(bool_encoding)
            btor2_annotations.append(sort_comment)

    return btor2_annotations


def to_btor2_const_arrays(
    context: moxi.Context, sort_map: SortMap, var_map: VarMap, expr_map: ExprMap
) -> list[btor.BtorNode]:
    """Returns a list of `btor.BtorNode`s that defines all constant arrays that are present in `context.const_arrays`. BTOR2 supports initializing array-sorted variables with bit-vectors. Each `(as const (Array X Y) val)` moxi. expression translates to a variable `Array_bv_X_Y_val` where `init(Array_bv_X_Y_val) = val` and `next(Array_bv_X_Y_val) = Array_bv_X_Y_val`."""
    btor2_const_arrays: list[btor.BtorNode] = []

    for sort, val, expr in context.const_arrays:
        sort_str = (
            (((str(sort)).replace("(", "")).replace(")", "")).replace("_ BitVec ", "bv")
        ).replace(" ", "_")
        const_str = f"{sort_str}_{val.value}"

        const_var = btor.BtorStateVar(sort_map[sort], const_str)

        build_expr_map(val, context, False, sort_map, var_map, expr_map)
        expr_map[expr] = const_var

        btor2_const_arrays.append(expr_map[val])
        btor2_const_arrays.append(const_var)
        btor2_const_arrays.append(btor.BtorInit(const_var, expr_map[val]))
        btor2_const_arrays.append(btor.BtorNext(const_var, const_var))

    return btor2_const_arrays


def to_btor2_var_definitions(
    context: moxi.Context,
    sort_map: SortMap,
    var_map: VarMap,
) -> list[btor.BtorNode]:
    """Returns a list of `btor.BtorNode`s that declare each value in `var_map` and define the proper `btor.BtorInit` and `btor.BtorNext` relations. Defines declared constants and have their next values set to their current values. Constrains enumeration-sorted variables such that their values can be no more than the number of potential values of their sort.

    Each key/value pair in `var_map` maps a `(moxi.Var, moxi.SystemContext)` to a triple of `btor.BtorStateVar`s, representing the initial, current, and next variants of the system-context-dependent `moxi.Var`. The current variant of each variable is initialized to the initial variant and the next value of the current variant is set to the next variant. For example, if there is an `moxi.Var` "var", that will map to a triple of `btor.BtorStateVar`s `(var.init, var.cur, var.next)` such that `init(var.cur) = var.init` and `next(var.cur) = var.next`.
    """
    btor2_var_definitions: list[btor.BtorNode] = []
    handled = set()
    const_vars = get_const_vars(context, var_map)

    for var_symbol, sys_ctx, (init, cur, next) in [
        (var_symbol, sys_ctx, btor_vars)
        for (var_symbol, sys_ctx), btor_vars in var_map.items()
    ]:
        # var_map may have repeat values (i.e., renamed variables point to same btor.Btor variables)
        if cur.symbol in handled:
            continue
        handled.add(cur.symbol)

        # for a variable const, define:
        #   next(const.cur) = const.cur
        if cur in const_vars:
            btor2_var_definitions.append(cur)
            btor2_var_definitions.append(
                btor.BtorNext(
                    cast(btor.BtorStateVar, cur), cast(btor.BtorStateVar, cur)
                )
            )
            continue

        btor2_var_definitions.append(init) if init else None
        btor2_var_definitions.append(cur) if cur else None
        btor2_var_definitions.append(next) if next else None

        top = sys_ctx.get_top()
        if not top:
            raise ValueError(f"System context for {var_symbol} is empty")

        (_, system) = top

        sort = system.get_sort(var_symbol)
        if not sort and cur in const_vars:
            sort = context.declared_consts[var_symbol]
        elif not sort:
            raise ValueError(f"Variable {var_symbol} does not exist in context")

        # TODO:
        if sort.symbol in context.declared_enum_sorts:
            num_enum_values = len(context.declared_enum_sorts[sort.symbol])

            btor2_max_num = btor.BtorConst(sort_map[sort], num_enum_values - 1)
            btor2_enum_lt = btor.BtorApply(
                sort_map[moxi.Sort.Bool()],
                btor.BtorOperator.ULTE,
                (None, None),
                (cur, btor2_max_num, None),
            )
            btor2_enum_constraint = btor.BtorConstraint(btor2_enum_lt)

            btor2_var_definitions.append(btor2_max_num)
            btor2_var_definitions.append(btor2_enum_lt)
            btor2_var_definitions.append(btor2_enum_constraint)

    for init, cur in [(i, c) for (i, c, _) in var_map.values() if i and c]:
        btor2_var_definitions.append(btor.BtorInit(cur, init))

    for cur, next in [(c, n) for (_, c, n) in var_map.values() if c and n]:
        btor2_var_definitions.append(btor.BtorNext(cur, next))

    return btor2_var_definitions


def to_btor2_reach_properties(
    check: moxi.CheckSystem,
    query: list[str],
    context: moxi.Context,
    sort_map: SortMap,
    var_map: VarMap,
    expr_map: ExprMap,
) -> list[btor.BtorNode]:
    """Returns a list of `btor.BtorNode`s corresponding to the set of `reachable` formulas in `query`.

    In BTOR2, multiple bad properties asks for a trace that satisfies at
    least one bad property. In moxi., multiple `:reach` properties asks for a
    trace that eventually satisfies every property listed.

    To solve this, we introduce a flag for each `:reach` property that
    remains true if the property is every true, then set the conjunction
    of all such flags as the bad property. The resulting witness is 1
    step longer than necessary, but we solve this in the witness
    translator by removing the final frame."""
    btor2_reach: list[btor.BtorNode] = []
    flag_vars: list[btor.BtorStateVar] = []
    btor_bool_sort = sort_map[moxi.Sort.Bool()]
    btor_true = btor.BtorConst(btor_bool_sort, 1)
    btor_false = btor.BtorConst(btor_bool_sort, 0)
    btor2_reach.append(btor_true)
    btor2_reach.append(btor_false)

    for reach_symbol, reach in [
        (symbol, expr) for symbol, expr in check.reachable.items() if symbol in query
    ]:
        build_expr_map(reach, context, False, sort_map, var_map, expr_map)
        btor2_reach += btor.flatten_btor2_expr(expr_map[reach])

        flag_var = btor.BtorStateVar(btor_bool_sort, f"{reach_symbol}__FLAG__")
        flag_next = btor.BtorApply(
            btor_bool_sort,
            btor.BtorOperator.ITE,
            (None, None),
            (flag_var, btor_true, expr_map[reach]),
        )

        btor2_reach.append(flag_var)
        btor2_reach.append(btor.BtorInit(flag_var, btor_false))
        btor2_reach.append(flag_next)
        btor2_reach.append(btor.BtorNext(flag_var, flag_next))

        flag_vars.append(flag_var)

    if len(flag_vars) == 1:
        bad_expr = flag_vars[0]
    elif len(flag_vars) > 1:
        bad_expr = btor.BtorApply(
            btor_bool_sort,
            btor.BtorOperator.AND,
            (None, None),
            (flag_vars[0], flag_vars[1], None),
        )
        for i in range(2, len(flag_vars)):
            bad_expr = btor.BtorApply(
                btor_bool_sort,
                btor.BtorOperator.AND,
                (None, None),
                (bad_expr, flag_vars[i], None),
            )
    else:
        bad_expr = btor_false

    btor2_reach += btor.flatten_btor2_expr(bad_expr)
    btor2_reach.append(btor.BtorBad(bad_expr))

    return btor2_reach


def to_btor2_check_system(
    check: moxi.CheckSystem,
    context: moxi.Context,
    sort_map: SortMap,
    var_map: VarMap,
    expr_map: ExprMap,
) -> dict[str, btor.BtorProgram]:
    """Returns a `dict` mapping query symbols to `btor.BtorProgram`s. Each query will have the same model but may have different "bad"/"fair" properties. First, we construct the reference BTOR2 model, then we map each query symbol to a new BTOR2 program with the reference model as a prefix and query formula constraints as a suffix."""
    btor2_programs: dict[str, btor.BtorProgram] = {}
    btor2_model: list[btor.BtorNode] = []

    btor2_model += to_btor2_annotations(check, context, var_map)

    for sort in sort_map.values():
        btor2_model.append(sort)

    btor2_model += to_btor2_const_arrays(context, sort_map, var_map, expr_map)
    btor2_model += to_btor2_var_definitions(context, sort_map, var_map)

    # Push check-system
    context.push_system(
        check.symbol, context.defined_systems[check.symbol], check.full_signature
    )

    btor2_model += to_btor2_define_system(
        context.defined_systems[check.symbol], context, sort_map, var_map, expr_map
    )

    # Pop check-system
    context.pop_system()

    if check.queries:
        log.error("Warning: ':queries' attribute unsupported, ignoring", FILE_NAME)

    for query_symbol, query in check.query.items():
        # shallow copy the prog since we don't want to lose sort_map/var_map
        btor2_prog = copy(btor2_model)

        for symbol, assume in [
            (symbol, expr)
            for symbol, expr in check.assumption.items()
            if symbol in query
        ]:
            btor2_prog += to_btor2_constraint(
                assume, context, False, sort_map, var_map, expr_map, f"assume {symbol}"
            )

        for fair in [
            expr for symbol, expr in check.fairness.items() if symbol in query
        ]:
            build_expr_map(fair, context, False, sort_map, var_map, expr_map)
            btor2_prog += btor.flatten_btor2_expr(expr_map[fair])
            btor2_prog.append(btor.BtorFair(expr_map[fair]))

        for symbol, current in [
            (symbol, expr) for symbol, expr in check.current.items() if symbol in query
        ]:
            btor2_prog += to_btor2_constraint(
                current, context, True, sort_map, var_map, expr_map, f"current {symbol}"
            )

        btor2_prog += to_btor2_reach_properties(
            check, query, context, sort_map, var_map, expr_map
        )

        log.debug(2, "Reducing BTOR2 program", FILE_NAME)
        reduced_btor2_prog = btor.assign_nids(btor2_prog)

        btor2_programs[query_symbol] = btor.BtorProgram(reduced_btor2_prog)

    return btor2_programs


def translate(
    moxi_program: moxi.Program, int_width: int
) -> Optional[btor.BtorProgramSet]:
    """Translate `moxi_prog` to an equisatisfiable set of btor.Btor programs, labeled by query symbol. Translates `Int` types to `BitVec`s of width `int_width`. Dumps a pickle file for each generated BTOR2 file if `do_pickle` is true.

    The strategy for translation is to sort check the input then construct a btor.Btor program for each query (and targeted system) by:
    1. Constructing a mapping of `moxi.Sort`s to `btor.BtorSort`s for the target system
    2. Constructing a mapping of `moxi.Var`s to `btor.BtorVar`s for the target system
    3. Translating the relevant model of the query
    4. Translating the query

    1-3 traverses the IL program starting from the target system and traversing down through the system's subsystems and init, trans, and inv expressions and 4 traverses the relevant attributes of the query.

    Note that the output programs will have input/output/local variables renamed based on the query, but all local subsystem variables will remain as defined."""
    (well_sorted, context) = moxi.sort_check(moxi_program)

    if not well_sorted:
        log.error("Failed sort check", FILE_NAME)
        return None
    log.debug(2, "Translating to BTOR2", FILE_NAME)

    # BTOR2 only supports bit vectors and their operations and
    # does not support functions, so we force all other types to
    # bit vectors and inline all functions
    moxi.inline_funs(moxi_program, context)
    moxi.to_binary_applys(moxi_program, context)
    moxi.to_qfbv(moxi_program, int_width)

    check_system_index: dict[str, int] = {}
    btor2_program_set: btor.BtorProgramSet = []

    for check_system in moxi_program.get_check_system_cmds():
        sys_symbol = check_system.symbol
        target_system = context.defined_systems[sys_symbol]

        sort_map: SortMap = {}
        var_map: VarMap = {}
        expr_map: ExprMap = {}

        build_sort_map_cmd(target_system, context, sort_map)
        build_sort_map_cmd(check_system, context, sort_map)
        build_var_map_cmd(check_system, context, sort_map, var_map)

        context.push_system(check_system.symbol, check_system, [])
        btor2_programs = to_btor2_check_system(
            check_system, context, sort_map, var_map, expr_map
        )
        context.pop_system()

        if sys_symbol not in check_system_index:
            check_system_index[sys_symbol] = 1

        check_system_index[sys_symbol] += 1

        btor2_program_set.append((sys_symbol, btor2_programs))

    return btor2_program_set


def translate_file(
    input_path: Path,
    output_path: Path,
    schema_path: Path,
    int_width: int,
    do_pickle: bool,
) -> int:
    if not input_path.is_file():
        log.error(f"'{input_path}' is not a valid file.", FILE_NAME)
        return 1

    if output_path.exists():
        log.error(f"Output path '{output_path}' already exists.", FILE_NAME)
        return 1

    if input_path.suffix == ".json":
        with open(str(input_path), "r") as file:
            program = json2moxi.from_json(schema_path, json.load(file))
    elif input_path.suffix == ".moxi":
        program = parse_moxi.parse(input_path)
    elif input_path.suffix == ".pickle":
        with open(str(input_path), "rb") as f:
            program = pickle.load(f)
    else:
        log.error(f"File format unsupported ({input_path.suffix})", FILE_NAME)
        return 1

    if not program:
        log.error("Failed parsing", FILE_NAME)
        return 1

    btor2_program_set = translate(program, int_width)

    if not btor2_program_set:
        log.error("Failed translation", FILE_NAME)
        return 1

    if not btor.write_btor2_program_set(
        btor2_program_set, output_path, do_pickle
    ):
        return 1

    return 0
