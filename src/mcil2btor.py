from copy import copy
import json
from pathlib import Path
import pickle
import time
from typing import cast

from .util import eprint
from .mcil import *
from .json2mcil import from_json
from .btor import *
from .parse_mcil import parse_mcil

FILE_NAME = Path(__file__).name

mcil_fun_map: dict[str, BtorOperator] = {
    "=": BtorOperator.EQ,
    "distinct": BtorOperator.NEQ,
    "=>": BtorOperator.IMPLIES,
    "iff": BtorOperator.IFF,
    "not": BtorOperator.NOT,
    "and": BtorOperator.AND,
    "or": BtorOperator.OR,
    "xor": BtorOperator.XOR,
    "ite": BtorOperator.ITE,
    "concat": BtorOperator.CONCAT,
    "extract": BtorOperator.SLICE,
    "zero_extend": BtorOperator.UEXT,
    "sign_extend": BtorOperator.SEXT,
    "rotate_left": BtorOperator.ROL,
    "rotate_right": BtorOperator.ROR,
    "bvshl": BtorOperator.SLL,
    "bvlshr": BtorOperator.SRL,
    "bvashr": BtorOperator.SRA,
    "bvnot": BtorOperator.NOT,
    "bvneg": BtorOperator.NEG,
    "bvand": BtorOperator.AND,
    "bvnand": BtorOperator.NAND,
    "bvor": BtorOperator.OR,
    "bvnor": BtorOperator.NOR,
    "bvxor": BtorOperator.XOR,
    "bvxnor": BtorOperator.XNOR,
    "bvadd": BtorOperator.ADD,
    "bvsub": BtorOperator.SUB,
    "bvmul": BtorOperator.MUL,
    "bvudiv": BtorOperator.UDIV,
    "bvsdiv": BtorOperator.SDIV,
    "bvurem": BtorOperator.UREM,
    "bvsrem": BtorOperator.SREM,
    "bvsmod": BtorOperator.SMOD,
    "bvult": BtorOperator.ULT,
    "bvule": BtorOperator.ULTE,
    "bvugt": BtorOperator.UGT,
    "bvuge": BtorOperator.UGTE,
    "bvslt": BtorOperator.SLT,
    "bvsle": BtorOperator.SLTE,
    "bvsgt": BtorOperator.SGT,
    "bvsge": BtorOperator.SGTE,
    "reduce_and": BtorOperator.REDAND,
    "reduce_or": BtorOperator.REDOR,
    "reduce_xor": BtorOperator.REDXOR,
    "select": BtorOperator.READ,
    "store": BtorOperator.WRITE 
}

# A SortMap maps MCILSorts to BTOR2 sorts
SortMap = dict[MCILSort, BtorSort]

# An ExprMap maps MCILExprs to BtorExprs
ExprMap = dict[MCILExpr, BtorExpr]

BtorVarType = tuple[Optional[BtorVar], Optional[BtorVar], Optional[BtorVar]]

# A VarMap maps variables in a system context to BTOR2 variables. BTOR2 variables are tuples by default (to handle
# initial, current, and next values) for output and state variables, whereas inputs are just a single variable.
VarMap = dict[tuple[MCILVar, MCILSystemContext], BtorVarType]

# A RenameMap maps variables in a system context to another variable and system context. This is used for mapping
# input/output variables of subsystem. The mapped-to variable/system context pair may also be in the rename map, in
# which case another lookup is necessary.
RenameMap = dict[tuple[MCILVar, MCILSystemContext], tuple[MCILVar, MCILSystemContext]]

def get_const_vars(context: MCILContext, var_map: VarMap):
    return {
        btor_cur 
        for (mcil_var,_),(_,btor_cur,_) in var_map.items() 
        if btor_cur and mcil_var.symbol in context.declared_consts.keys()
    }

def get_const_array_init_vars(context: MCILContext, var_map: VarMap):
    return {
        btor_init : mcil_var 
        for (mcil_var,_),(btor_init,_,_) in var_map.items() 
        if btor_init and mcil_var in context.const_array_init_exprs.keys()
    }

def rename_lookup(
    var: MCILVar, 
    system_context: MCILSystemContext, 
    rename_map: RenameMap
) -> tuple[MCILVar, MCILSystemContext]:
    """Returns the variable and context to map the `var`/`system_context` pair to."""
    cur_var, cur_system_context = var, system_context
    while (cur_var, cur_system_context) in rename_map:
        (cur_var, cur_system_context) = rename_map[(cur_var, cur_system_context)]
    return (cur_var, cur_system_context)


def update_rename_map(
    system_context: MCILSystemContext,
    target_system: MCILDefineSystem,
    target_system_symbol: str,
    signature: list[MCILVar],
    target_signature: list[MCILVar],
    rename_map: RenameMap
) -> None:
    target_context = system_context.copy() # need to copy (only copies pointers)
    target_context.push((target_system_symbol, target_system))
    for cmd_var,target_var in zip(signature, target_signature):
        rename_map[(target_var, target_context)] = (cmd_var, system_context.copy())


def mcilsort2btorsort(sort: MCILSort, context: MCILContext, sort_map: SortMap) -> BtorSort:
    if sort in sort_map:
        return sort_map[sort]
    elif is_bool_sort(sort):
        return BtorBitVec(1)
    elif is_bitvec_sort(sort):
        return BtorBitVec(sort.identifier.indices[0])
    elif is_array_sort(sort):
        return BtorArray(mcilsort2btorsort(sort.parameters[0], context, sort_map), 
                          mcilsort2btorsort(sort.parameters[1], context, sort_map))
    elif sort.identifier.symbol in context.declared_enum_sorts:
        width = len(context.declared_enum_sorts[sort.identifier.symbol]).bit_length()
        return BtorBitVec(width)
    else:
        raise NotImplementedError(f"MCIL sort '{sort}' ({type(sort)}) unrecognized")


def build_sort_map_expr(
    node: MCILExpr,
    context: MCILContext,
    sort_map: SortMap
) -> SortMap:
    """Iteratively recurse the expr IL and map each unique MCILSort of each node to a new BtorSort."""
    for expr in postorder_mcil(node, context):
        if expr.sort not in sort_map:
            sort_map[expr.sort] = mcilsort2btorsort(expr.sort, context, sort_map)

    return sort_map


def build_sort_map_cmd(
    cmd: MCILCommand, 
    context: MCILContext,
    sort_map: SortMap
) -> SortMap:
    if isinstance(cmd, MCILDefineSystem):
        for subsystem in cmd.subsystems.values():
            build_sort_map_cmd(subsystem,context, sort_map)

        build_sort_map_expr(cmd.init,context, sort_map)
        build_sort_map_expr(cmd.trans,context, sort_map)
        build_sort_map_expr(cmd.inv, context, sort_map)
    elif isinstance(cmd, MCILCheckSystem):
        for assume in cmd.assumption.values():
            build_sort_map_expr(assume,context, sort_map)
        for fair in cmd.fairness.values():
            build_sort_map_expr(fair,context, sort_map)
        for reach in cmd.reachable.values():
            build_sort_map_expr(reach,context, sort_map)
        for current in cmd.current.values():
            build_sort_map_expr(current,context, sort_map)
    else:
        raise NotImplementedError

    return sort_map


def build_var_map_expr(
    node: MCILExpr,
    context: MCILContext,
    rename_map: RenameMap,
    sort_map: SortMap,
    var_map: VarMap
) -> None:
    """Iteratively recurse the expr IL and map each input MCILVar to a single BtorInput and each local/output var to a
    triple of BtorStates corresponding to that var's init, cur, and next values."""
    for expr in postorder_mcil(node, context):
        if isinstance(expr, MCILVar) and (expr, context.system_context) not in var_map:
            var, system_context = rename_lookup(expr, context.system_context, rename_map)

            symbol = "::".join(system_context.get_scope_symbols() + [var.symbol])

            # note: those system context copies only copy the pointers + they are only as big as the subsystems are deep
            if var.var_type == MCILVarType.INPUT:
                var_map[(expr, context.system_context.copy())] = (
                    None,
                    BtorStateVar(sort_map[var.sort], f"{symbol}.cur"),
                    BtorStateVar(sort_map[var.sort], f"{symbol}.next")
                )
            elif var.var_type == MCILVarType.OUTPUT or var.var_type == MCILVarType.LOCAL:
                var_map[(expr, context.system_context.copy())] = (
                    BtorStateVar(sort_map[var.sort], f"{symbol}.init"),
                    BtorStateVar(sort_map[var.sort], f"{symbol}.cur"),
                    BtorStateVar(sort_map[var.sort], f"{symbol}.next")
                )
            elif var.symbol in context.declared_consts: 
                var_map[(expr, context.system_context.copy())] = (
                    None,
                    BtorStateVar(sort_map[var.sort], f"{symbol}.cur"),
                    None
                )
            # else var is a bound variable, skip


def build_var_map_cmd(
    cmd: MCILCommand, 
    context: MCILContext,
    rename_map: RenameMap,
    sort_map: SortMap,
    var_map: VarMap
) -> None:
    """Update var_map to map all MCILVar instances to BtorVars"""
    if isinstance(cmd, MCILDefineSystem):
        for (subsys_symbol, subsystem) in cmd.subsystems.items():
            signature: list[MCILVar] = []
            for symbol in cmd.subsystem_signatures[subsys_symbol][1]:
                sys_vars = cmd.input_vars + cmd.output_vars + cmd.local_vars
                for var in [v for v in sys_vars if v.symbol == symbol]:
                    signature.append(var)

            target_signature = subsystem.input_vars + subsystem.output_vars

            update_rename_map(context.system_context, subsystem, subsys_symbol, 
                signature, target_signature, rename_map)
            
            context.system_context.push((subsys_symbol, subsystem))
            build_var_map_cmd(subsystem, context, rename_map, sort_map, var_map)
            context.system_context.pop()

        build_var_map_expr(cmd.init, context, rename_map, sort_map, var_map)
        build_var_map_expr(cmd.trans, context, rename_map, sort_map, var_map)
        build_var_map_expr(cmd.inv, context, rename_map, sort_map, var_map)
    elif isinstance(cmd, MCILCheckSystem):
        for assume in cmd.assumption.values():
            build_var_map_expr(assume, context, rename_map, sort_map, var_map)
        for fair in cmd.fairness.values():
            build_var_map_expr(fair, context, rename_map, sort_map, var_map)
        for reach in cmd.reachable.values():
            build_var_map_expr(reach, context, rename_map, sort_map, var_map)
        for current in cmd.current.values():
            build_var_map_expr(current, context, rename_map, sort_map, var_map)

        target_system = context.defined_systems[cmd.sys_symbol]
        signature = cmd.input_vars + cmd.output_vars + cmd.local_vars
        target_signature = target_system.input_vars + target_system.output_vars + target_system.local_vars

        update_rename_map(context.system_context, target_system, target_system.symbol, 
            signature, target_signature, rename_map)

        context.system_context.push((cmd.sys_symbol, target_system))
        build_var_map_cmd(target_system, context, rename_map, sort_map, var_map)        
        context.system_context.pop()
    else:
        raise NotImplementedError


def build_expr_map(
    node: MCILExpr, 
    context: MCILContext,
    is_init_expr: bool,
    sort_map: SortMap,
    var_map: VarMap,
    expr_map: ExprMap
) -> None:
    for expr in postorder_mcil(node, context):
        if isinstance(expr, MCILVar) and expr.symbol in context.bound_let_vars:
            expr_map[expr] = expr_map[context.bound_let_vars[expr.symbol]]
        elif isinstance(expr, MCILVar) and all([b for b in var_map[(expr, context.system_context)]]):
            # We use "int(not is_init_expr) + int(expr.prime)" to compute the index in var_map tuple:
            #   var_map[var] = (init, cur, next)
            idx = int(not is_init_expr) + int(expr.prime)
            btor_var = var_map[(expr, context.system_context)][idx]

            if not btor_var:
                symbol = '::'.join(context.system_context.get_scope_symbols() + [expr.symbol])
                raise ValueError(f"No BTOR2 var for {symbol}")
                
            expr_map[expr] = btor_var
        elif isinstance(expr, MCILVar):
            # We use "int(expr.prime)" to compute the index in var_map tuple:
            #   var_map[var] = (init, cur, next)
            idx = 1 + int(expr.prime)
            btor_var = var_map[(expr, context.system_context)][idx]

            if not btor_var:
                symbol = '::'.join(context.system_context.get_scope_symbols() + [expr.symbol])
                raise ValueError(f"No BTOR2 var for {symbol}")

            expr_map[expr] = btor_var
        elif isinstance(expr, MCILConstant) and expr.sort.identifier.symbol in context.declared_enum_sorts:
            value = context.declared_enum_sorts[expr.sort.identifier.symbol].index(expr.value)
            expr_map[expr] = BtorConst(sort_map[expr.sort], value)
        elif isinstance(expr, MCILConstant):
            expr_map[expr] = BtorConst(sort_map[expr.sort], expr.value)
        elif is_init_expr and is_const_array_expr(expr):
            pass 
        elif is_init_expr and is_const_array_init_expr(expr):
            expr_map[expr] = BtorConst(sort_map[MCIL_BOOL_SORT], True)
        elif isinstance(expr, MCILApply) and expr.identifier.symbol in mcil_fun_map:
            if len(expr.children) > 3:
                raise NotImplementedError(f"{expr}")

            tmp_indices = copy(expr.identifier.indices) + ([None] * (2 - len(expr.identifier.indices)))
            (idx1, idx2) = tuple(tmp_indices)

            tmp_children = copy(expr.children) + ([None] * (3 - len(expr.children)))
            (arg1, arg2, arg3) = tuple(tmp_children)

            btor2_args = (expr_map[arg1] if arg1 else None,
                          expr_map[arg2] if arg2 else None,
                          expr_map[arg3] if arg3 else None)

            expr_map[expr] = BtorApply(
                sort_map[expr.sort], 
                mcil_fun_map[expr.identifier.symbol], 
                (idx1, idx2),
                btor2_args
            )
        elif isinstance(expr, MCILLetExpr):
            expr_map[expr] = expr_map[expr.get_expr()]
        else:
            raise NotImplementedError(f"Unsupported expression '{expr}'")


def translate_define_system(
    btor2_model: list[BtorNode],
    system: MCILDefineSystem, 
    context: MCILContext,
    sort_map: SortMap,
    var_map: VarMap,
    expr_map: ExprMap
) -> None:
    for symbol,subsystem in system.subsystems.items():
        context.system_context.push((symbol, subsystem))
        translate_define_system(btor2_model, subsystem, context, sort_map, var_map, expr_map)
        context.system_context.pop()

    build_expr_map(system.init, context, True, sort_map, var_map, expr_map)
    btor2_model += flatten_btor2_expr(expr_map[system.init])
    btor2_model.append(BtorConstraint(expr_map[system.init]))

    system_symbol = "::".join(context.system_context.get_scope_symbols())
    btor2_model[-1].set_comment(f"init {system_symbol}")

    # type-checking hack: check for len instead of InputVar/StateVar
    # recall that consts and const-initialized arrays are already handled
    for init,cur in [(i,c) for (mcil_var,_),(i,c,_) in var_map.items() if (i and c and mcil_var not in context.const_array_init_exprs.keys())]: 
        btor2_model.append(BtorInit(cast(BtorStateVar, cur), init))

    build_expr_map(system.trans, context, False, sort_map, var_map, expr_map)
    btor2_model += flatten_btor2_expr(expr_map[system.trans])
    btor2_model.append(BtorConstraint(expr_map[system.trans]))
    btor2_model[-1].set_comment(f"trans {system_symbol}")

    for cur,next in [(c,n) for (_,c,n) in var_map.values() if c and n]:
        btor2_model.append(BtorNext(cast(BtorStateVar, cur), next))

    build_expr_map(system.inv, context, False, sort_map, var_map, expr_map)
    btor2_model += flatten_btor2_expr(expr_map[system.inv])
    btor2_model.append(BtorConstraint(expr_map[system.inv]))
    btor2_model[-1].set_comment(f"inv {system_symbol}")


def translate_check_system(
    check: MCILCheckSystem, 
    context: MCILContext,
    sort_map: SortMap,
    var_map: VarMap,
    expr_map: ExprMap
) -> dict[str, list[BtorNode]]:
    """A check_system command can have many queries: each query will have the same target system but may correspond to different models of that system. First, we construct that reference BTOR2 model, then for each query we generate a new BTOR2 program with the reference model as a prefix and query as a suffix."""
    btor2_prog_list: dict[str, list[BtorNode]] = {}
    btor2_model: list[BtorNode] = []

    for sort in sort_map.values():
        btor2_model.append(sort)

    # Note: var_map may have repeat values (i.e., renamed variables point to same Btor variables)
    const_vars = get_const_vars(context, var_map)
    const_array_init_vars = get_const_array_init_vars(context, var_map)
    for (init,cur,next) in set(var_map.values()):
        if cur in const_vars:
            btor2_model.append(cur)

            btor2_model.append(BtorNext(
                    cast(BtorStateVar, cur), 
                    cast(BtorStateVar, cur)
            ))

            continue
        
        if init in const_array_init_vars and cur and next:
            const_val = context.const_array_init_exprs[const_array_init_vars[init]]

            build_expr_map(const_val, context, True, sort_map, var_map, expr_map)

            btor2_model.append(expr_map[const_val])
            btor2_model.append(init)
            btor2_model.append(cur)
            btor2_model.append(next)

            btor2_model.append(BtorInit(cast(BtorStateVar, cur), expr_map[const_val]))

            continue

        btor2_model.append(init) if init else None
        btor2_model.append(cur) if cur else None
        btor2_model.append(next) if next else None

    context.system_context.push((check.sys_symbol, context.defined_systems[check.sys_symbol]))

    translate_define_system(btor2_model, context.defined_systems[check.sys_symbol], context, sort_map, var_map, expr_map)

    context.system_context.pop()

    if check.queries:
        eprint(f"[{FILE_NAME}] ':queries' attribute unsupported, ignoring")

    for symbol,query in check.query.items():
        # shallow copy the prog since we don't want to lose sort_map/var_map
        btor2_prog = copy(btor2_model)

        for assume in [expr for symbol,expr in check.assumption.items() if symbol in query]:
            build_expr_map(assume, context, False, sort_map, var_map, expr_map)
            btor2_prog += flatten_btor2_expr(expr_map[assume])
            btor2_prog.append(BtorConstraint(expr_map[assume]))
        
        for fair in [expr for symbol,expr in check.fairness.items() if symbol in query]:
            build_expr_map(fair, context, False, sort_map, var_map, expr_map)
            btor2_prog += flatten_btor2_expr(expr_map[fair])
            btor2_prog.append(BtorFair(expr_map[fair]))
    
        for current in [expr for symbol,expr in check.current.items() if symbol in query]:
            build_expr_map(current, context, True, sort_map, var_map, expr_map)
            btor2_prog += flatten_btor2_expr(expr_map[current])
            btor2_prog.append(BtorConstraint(expr_map[current]))

        # Handle reachability properties:
        #
        # In BTOR2, multiple bad properties asks for a trace that satisfies at least one
        # bad property. In MCIL, multiple :reach properties asks for a trace that eventually
        # satisfies every property listed. 
        #
        # To solve this, we introduce a flag for each :reach property that remains true if the
        # property is every true, then set the conjunction of all such flags as the bad property.
        # The resulting witness will be 1 step longer than necessary, but we can solve this in the
        # witness translator.
        flag_vars = []
        btor_bool_sort = sort_map[MCIL_BOOL_SORT]
        btor_true = BtorConst(btor_bool_sort, 1)
        btor_false = BtorConst(btor_bool_sort, 0)
        btor2_prog.append(btor_true)
        btor2_prog.append(btor_false)

        for symbol,reach in [
            (symbol,expr) for symbol,expr in check.reachable.items() if symbol in query
        ]:
            build_expr_map(reach, context, False, sort_map, var_map, expr_map)
            btor2_prog += flatten_btor2_expr(expr_map[reach])

            flag_var = BtorStateVar(btor_bool_sort, f"{symbol}__FLAG__")
            flag_next = BtorApply(btor_bool_sort, BtorOperator.ITE, (None, None),
                (flag_var, btor_true, expr_map[reach])
            )

            btor2_prog.append(flag_var)
            btor2_prog.append(BtorInit(flag_var, btor_false))
            btor2_prog.append(flag_next)
            btor2_prog.append(BtorNext(flag_var, flag_next))

            flag_vars.append(flag_var)

        if len(flag_vars) == 1:
            bad_expr = flag_vars[0]
        elif len(flag_vars) > 1:
            bad_expr = BtorApply(btor_bool_sort, BtorOperator.AND, (None, None), 
                (flag_vars[0], flag_vars[1], None)
            )
            for i in range(2, len(flag_vars)):
                bad_expr = BtorApply(btor_bool_sort, BtorOperator.AND, (None, None), 
                    (bad_expr, flag_vars[i], None)
                )
        else:
            bad_expr = btor_false
            
        btor2_prog += flatten_btor2_expr(bad_expr)
        btor2_prog.append(BtorBad(bad_expr))
        # end handling reachability properties

        print(f"[{FILE_NAME}] reducing BTOR2 program")
        reduced_btor2_prog = assign_nids(btor2_prog)

        btor2_prog_list[symbol] = reduced_btor2_prog

    return btor2_prog_list
    

def translate(mcil_prog: MCILProgram) -> Optional[dict[str, dict[str, list[BtorNode]]]]:
    """Translate `mcil_prog` to an equisatisfiable set of Btor programs, labeled by query symbol.
    
    The strategy for translation is to sort check the input then construct a Btor program for each query (and targeted system) by:
    1) Constructing a mapping of MCILSorts to BtorSorts for the target system
    2) Constructing a mapping of MCILVars to BtorVars for the target system
    3) Translating the relevant model of the query 
    4) Translating the query

    1-3 traverses the IL program starting from the target system and traversing down through the system's init, trans, and inv expressions as well as any subsystems and 4 traverses the relevant attributes of the query.

    Note that the output programs will have input/output/local variables renamed based on the query, but all subsystem variables will remain as defined.
    """
    (well_sorted, context) = sort_check(mcil_prog)

    if not well_sorted:
        eprint(f"[{FILE_NAME}] failed sort check\n")
        return None
    print(f"[{FILE_NAME}] translating to BTOR2")
    
    # BTOR2 only supports bit vectors and their operations and 
    # does not support functions, so we force all other types to 
    # bit vectors and inline all functions
    inline_funs(mcil_prog, context)
    to_binary_applys(mcil_prog, context)
    to_qfbv(mcil_prog)

    btor2_prog_list: dict[str, dict[str, list[BtorNode]]] = {}
    sort_map: SortMap = {}
    var_map: VarMap = {}
    expr_map: ExprMap = {}

    for check_system in mcil_prog.get_check_system_cmds():
        target_system = context.defined_systems[check_system.sys_symbol]

        build_sort_map_cmd(target_system,context, sort_map)
        build_sort_map_cmd(check_system,context, sort_map)
        build_var_map_cmd(check_system, context, {}, sort_map, var_map)

        btor2_prog_list[check_system.sys_symbol] = (translate_check_system(check_system, context, sort_map, var_map, expr_map))

    print(f"[{FILE_NAME}] finished BTOR2 translation")

    return btor2_prog_list


def main(
    input_path: Path, 
    output_path: Path, 
    pickle_path: Optional[Path]
) -> int:
    if not input_path.is_file():
        eprint(f"[{FILE_NAME}]  '{input_path}' is not a valid file.\n")
        return 1

    if output_path.is_file():
        eprint(f"[{FILE_NAME}]  '{output_path}' is a file.\n")
        return 1

    if not output_path.is_dir():
        output_path.mkdir()

    with open(input_path, "r") as file:
        if input_path.suffix == ".json":
            program = from_json(json.load(file))
        elif input_path.suffix == ".mcil":
            program = parse_mcil(file.read())
        else:
            eprint(f"[{FILE_NAME}] file format unsupported ({input_path.suffix})\n")
            return 1

    if not program:
        eprint(f"[{FILE_NAME}] failed parsing\n")
        return 1

    output = translate(program)

    if output is None:
        eprint(f"[{FILE_NAME}] failed translation\n")
        return 1

    check_system_index = 0
    for (sys_symbol, check_system) in output.items():
        check_system_path = output_path / f"check-system-{sys_symbol}-{check_system_index}"
        if not check_system_path.is_dir():
            check_system_path.mkdir()

        for label, nodes in check_system.items():
            output_file_path = check_system_path / f"{input_path.stem}.{label}.btor"
            print(f"[{FILE_NAME}] writing BTOR2 output to {output_file_path}")

            with open(str(output_file_path), "w") as f:
                f.write("\n".join([str(n) for n in nodes])) 
                f.write("\n")

            if pickle_path:
                with open(pickle_path, "wb") as f:
                    pickle.dump(nodes, f)
    
    return 0
