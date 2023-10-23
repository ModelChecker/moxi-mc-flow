import argparse
from copy import copy
import json
import os
from pathlib import Path
import pickle
import sys
from typing import cast

from il import *
from json2il import from_json
from btor import *
from parse import parse_il

ilfunc_map: dict[str, BtorOperator] = {
    "=": BtorOperator.EQ,
    "!=": BtorOperator.NEQ,
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

# A SortMap maps ILSorts to BTOR2 sorts
SortMap = dict[ILSort, BtorSort]

InputVar = tuple[BtorVar, BtorVar] # :input variables
StateVar = tuple[BtorVar, BtorVar, BtorVar] # :local, :output variables

# A VarMap maps variables in a system context to BTOR2 variables. BTOR2 variables are tuples by default (to handle
# initial, current, and next values) for output and state variables, whereas inputs are just a single variable.
VarMap = dict[tuple[ILVar, ILSystemContext], InputVar | StateVar]

# A RenameMap maps variables in a system context to another variable and system context. This is used for mapping
# input/output variables of subsystem. The mapped-to variable/system context pair may also be in the rename map, in
# which case another lookup is necessary.
RenameMap = dict[tuple[ILVar, ILSystemContext], tuple[ILVar, ILSystemContext]]


def rename_lookup(
    var: ILVar, 
    system_context: ILSystemContext, 
    rename_map: RenameMap
) -> tuple[ILVar, ILSystemContext]:
    """Returns the variable and context to map the `var`/`system_context` pair to."""
    cur_var, cur_system_context = var, system_context
    while (cur_var, cur_system_context) in rename_map:
        (cur_var, cur_system_context) = rename_map[(cur_var, cur_system_context)]
    return (cur_var, cur_system_context)


def update_rename_map(
    system_context: ILSystemContext,
    target_system: ILDefineSystem,
    target_system_symbol: str,
    signature: list[ILVar],
    target_signature: list[ILVar],
    rename_map: RenameMap
):
    target_context = system_context.copy() # need to copy (only copies pointers)
    target_context.push((target_system_symbol, target_system))
    for cmd_var,target_var in zip(signature, target_signature):
        rename_map[(target_var, target_context)] = (cmd_var, system_context.copy())


def ilsort_to_btor2(sort: ILSort, enums: dict[str, int], sort_map: SortMap) -> BtorSort:
    if sort in sort_map:
        return sort_map[sort]
    elif is_bool_sort(sort):
        return BtorBitVec(1)
    elif is_bitvec_sort(sort):
        return BtorBitVec(sort.identifier.indices[0])
    elif is_array_sort(sort):
        return BtorArray(ilsort_to_btor2(sort.parameters[0], enums, sort_map), 
                          ilsort_to_btor2(sort.parameters[1], enums, sort_map))
    elif sort.identifier.symbol in enums:
        return BtorBitVec(enums[sort.identifier.symbol])
    else:
        raise NotImplementedError


def build_sort_map_expr(expr: ILExpr, enums: dict[str, int], sort_map: SortMap) -> SortMap:
    """Iteratively recurse the expr IL and map each unique ILSort of each node to a new BtorSort."""
    def build_sort_map_util(cur: ILExpr):
        if cur.sort not in sort_map:
            sort_map[cur.sort] = ilsort_to_btor2(cur.sort, enums, sort_map)
    
    postorder_iterative(expr, build_sort_map_util)
    return sort_map


def build_sort_map_cmd(cmd: ILCommand, enums: dict[str, int], sort_map: SortMap) -> SortMap:
    if isinstance(cmd, ILDefineSystem):
        for subsystem in cmd.subsystems.values():
            build_sort_map_cmd(subsystem, enums, sort_map)

        build_sort_map_expr(cmd.init, enums, sort_map)
        build_sort_map_expr(cmd.trans, enums, sort_map)
        build_sort_map_expr(cmd.inv,enums,  sort_map)
    elif isinstance(cmd, ILCheckSystem):
        for assume in cmd.assumption.values():
            build_sort_map_expr(assume, enums, sort_map)
        for fair in cmd.fairness.values():
            build_sort_map_expr(fair, enums, sort_map)
        for reach in cmd.reachable.values():
            build_sort_map_expr(reach, enums, sort_map)
        for current in cmd.current.values():
            build_sort_map_expr(current, enums, sort_map)
    else:
        raise NotImplementedError

    return sort_map


def build_var_map_expr(
    expr: ILExpr,
    context: ILContext,
    rename_map: RenameMap,
    sort_map: SortMap,
    var_map: VarMap):
    """Iteratively recurse the expr IL and map each input ILVar to a single BtorInput and each local/output var to a
    triple of BtorStates corresponding to that var's init, cur, and next values."""
    def build_var_map_util(expr: ILExpr):
        if isinstance(expr, ILVar) and (expr, context.system_context) not in var_map:
            var, system_context = rename_lookup(expr, context.system_context, rename_map)

            symbol = "::".join(system_context.get_scope_symbols() + [var.symbol])

            # note: those system context copies only copy the pointers + they are only as big as the subsystems are deep
            if var.var_type == ILVarType.INPUT:
                var_map[(expr, context.system_context.copy())] = (BtorStateVar(sort_map[var.sort], f"{symbol}.cur"),
                                                 BtorStateVar(sort_map[var.sort], f"{symbol}.next"))
            elif var.var_type == ILVarType.OUTPUT or var.var_type == ILVarType.LOCAL:
                var_map[(expr, context.system_context.copy())] = (BtorStateVar(sort_map[var.sort], f"{symbol}.init"),
                                                 BtorStateVar(sort_map[var.sort], f"{symbol}.cur"),
                                                 BtorStateVar(sort_map[var.sort], f"{symbol}.next"))

    postorder_iterative(expr, build_var_map_util)


def build_var_map_cmd(
    cmd: ILCommand, 
    context: ILContext,
    rename_map: RenameMap,
    sort_map: SortMap,
    var_map: VarMap):
    """Update var_map to map all ILVar instances to BtorVars"""
    if isinstance(cmd, ILDefineSystem):
        for (subsys_symbol, subsystem) in cmd.subsystems.items():
            signature_1: list[ILVar] = []
            for symbol in cmd.subsystem_signatures[subsys_symbol][1]:
                for var in cmd.input + cmd.output + cmd.local:
                    if var.symbol == symbol:
                        signature_1.append(var)

            # _,var_symbols = cmd.subsystem_signatures[subsys_symbol]
            # signature_2 = [subsystem.symbol_map[symbol] for symbol in var_symbols]

            target_signature = subsystem.input + subsystem.output

            update_rename_map(context.system_context, subsystem, subsys_symbol, signature_1, target_signature, rename_map)
            
            context.system_context.push((subsys_symbol, subsystem))
            build_var_map_cmd(subsystem, context, rename_map, sort_map, var_map)
            context.system_context.pop()

        build_var_map_expr(cmd.init, context, rename_map, sort_map, var_map)
        build_var_map_expr(cmd.trans, context, rename_map, sort_map, var_map)
        build_var_map_expr(cmd.inv, context, rename_map, sort_map, var_map)
    elif isinstance(cmd, ILCheckSystem):
        for assume in cmd.assumption.values():
            build_var_map_expr(assume, context, rename_map, sort_map, var_map)
        for fair in cmd.fairness.values():
            build_var_map_expr(fair, context, rename_map, sort_map, var_map)
        for reach in cmd.reachable.values():
            build_var_map_expr(reach, context, rename_map, sort_map, var_map)
        for current in cmd.current.values():
            build_var_map_expr(current, context, rename_map, sort_map, var_map)

        target_system = context.defined_systems[cmd.sys_symbol]
        signature_2 = cmd.input + cmd.output + cmd.local
        target_signature = target_system.input + target_system.output + target_system.local

        update_rename_map(context.system_context, target_system, target_system.symbol, signature_2, target_signature, rename_map)

        context.system_context.push((cmd.sys_symbol, target_system))
        build_var_map_cmd(target_system, context, rename_map, sort_map, var_map)        
        context.system_context.pop()
    else:
        raise NotImplementedError


def ilexpr_to_btor2(
    expr: ILExpr, 
    context: ILContext,
    is_init_expr: bool,
    sort_map: SortMap,
    var_map: VarMap
) -> BtorExpr:
    if isinstance(expr, ILVar) and len(var_map[(expr, context.system_context)]) == 3:
        # We use "int(not is_init_expr) + int(expr.prime)" to compute the index in var_map tuple:
        #   var_map[var] = (init, cur, next)
        idx = int(not is_init_expr) + (expr.prime)
        return cast(tuple[BtorVar,BtorVar,BtorVar], var_map[(expr, context.system_context)])[idx]
    elif isinstance(expr, ILVar) and len(var_map[(expr, context.system_context)]) == 2:
        # We use "int(expr.prime)" to compute the index in var_map tuple:
        #   var_map[var] = (cur, next)
        idx = int(expr.prime)
        return cast(tuple[BtorVar,BtorVar], var_map[(expr, context.system_context)])[idx]
    elif isinstance(expr, ILConstant) and expr.sort.identifier.symbol in context.declared_enum_sorts:
        value = context.declared_enum_sorts[expr.sort.identifier.symbol].index(expr.value)
        return BtorConst(sort_map[expr.sort], value)
    elif isinstance(expr, ILConstant):
        return BtorConst(sort_map[expr.sort], expr.value)
    elif isinstance(expr, ILApply):
        if len(expr.children) > 3:
            raise NotImplementedError

        tmp_children = copy(expr.children) + ([None] * (3 - len(expr.children)))
        (arg1, arg2, arg3) = tuple(tmp_children)

        btor2_args = (ilexpr_to_btor2(arg1, context, is_init_expr, sort_map, var_map) if arg1 else None,
                      ilexpr_to_btor2(arg2, context, is_init_expr, sort_map, var_map) if arg2 else None,
                      ilexpr_to_btor2(arg3, context, is_init_expr, sort_map, var_map) if arg3 else None)

        return BtorApply(sort_map[expr.sort], ilfunc_map[expr.identifier.symbol], btor2_args)

    raise NotImplementedError


def flatten_btor2_expr(expr: BtorExpr) -> list[BtorExpr]:
    out: list[BtorExpr] = []
    postorder_iterative_btor2(expr, lambda cur: out.append(cur))
    return out


def ilsystem_to_btor2(
    btor2_model: list[BtorNode],
    system: ILDefineSystem, 
    context: ILContext,
    sort_map: SortMap,
    var_map: VarMap):
    for symbol,subsystem in system.subsystems.items():
        context.system_context.push((symbol, subsystem))
        ilsystem_to_btor2(btor2_model, subsystem, context, sort_map, var_map)
        context.system_context.pop()

    btor2_init = ilexpr_to_btor2(system.init, context, True, sort_map, var_map)
    btor2_model += flatten_btor2_expr(btor2_init)
    btor2_model.append(BtorConstraint(btor2_init))
    btor2_model[-1].set_comment(f"init {system.symbol}")

    # type-checking hack: check for len instead of InputVar/StateVar
    for btor2_var in [v for v in var_map.values() if len(v) == 3]: 
        (init, cur, _) = btor2_var
        btor2_model.append(BtorInit(cast(BtorStateVar, cur), init))

    btor2_trans = ilexpr_to_btor2(system.trans, context, False, sort_map, var_map)
    btor2_model += flatten_btor2_expr(btor2_trans)
    btor2_model.append(BtorConstraint(btor2_trans))
    btor2_model[-1].set_comment(f"trans {system.symbol}")

    for btor2_var in var_map.values():
        if len(btor2_var) == 3:
            (_, cur, next) = btor2_var
            btor2_model.append(BtorNext(cast(BtorStateVar, cur), next))
        elif len(btor2_var) == 2:
            (cur, next) = btor2_var
            btor2_model.append(BtorNext(cast(BtorStateVar, cur), next))

    btor2_inv = ilexpr_to_btor2(system.inv, context, False, sort_map, var_map)
    btor2_model += flatten_btor2_expr(btor2_inv)
    btor2_model.append(BtorConstraint(btor2_inv))
    btor2_model[-1].set_comment(f"inv {system.symbol}")


def ilchecksystem_to_btor2(
    check: ILCheckSystem, 
    context: ILContext,
    sort_map: SortMap,
    var_map: VarMap
) -> dict[str, list[BtorNode]]:
    """A check_system command can have many queries: each query will have the same target system but may correspond to different models of that system. First, we construct that reference BTOR2 model, then for each query we generate a new BTOR2 program with the reference model as a prefix and query as a suffix."""
    btor2_prog_list: dict[str, list[BtorNode]] = {}
    btor2_model: list[BtorNode] = []

    for sort in sort_map.values():
        btor2_model.append(sort)

    # Note: var_map may have repeat values (i.e., renamed variables point to same Btor variables)
    for btor2_var in set(var_map.values()):
        if len(btor2_var) == 3:
            (init, cur, next) = btor2_var
            btor2_model.append(init)
            btor2_model.append(cur)
            btor2_model.append(next)
        elif len(btor2_var) == 2:
            (cur, next) = btor2_var
            btor2_model.append(cur)
            btor2_model.append(next)

    context.system_context.push((check.sys_symbol, context.defined_systems[check.sys_symbol]))
    ilsystem_to_btor2(btor2_model, context.defined_systems[check.sys_symbol], context, sort_map, var_map)
    context.system_context.pop()

    for sym, query in check.query.items():
        # shallow copy the prog since we don't want to lose sort_map/var_map
        btor2_prog = copy(btor2_model)

        for assume in [a[1] for a in check.assumption.items() if a[0] in query]:
            btor2_assume = ilexpr_to_btor2(assume, context, False, sort_map, var_map)
            btor2_prog += flatten_btor2_expr(btor2_assume)
            btor2_prog.append(BtorConstraint(btor2_assume))

        for reach in [r[1] for r in check.reachable.items() if r[0] in query]:
            btor2_reach = ilexpr_to_btor2(reach, context, False, sort_map, var_map)
            btor2_prog += flatten_btor2_expr(btor2_reach)
            btor2_prog.append(BtorBad(btor2_reach))
        
        for fair in [f[1] for f in check.fairness.items() if f[0] in query]:
            btor2_fair = ilexpr_to_btor2(fair, context, False, sort_map, var_map)
            btor2_prog += flatten_btor2_expr(btor2_fair)
            btor2_prog.append(BtorFair(btor2_fair))
    
        for current in [c[1] for c in check.current.items() if c[0] in query]:
            btor2_current = ilexpr_to_btor2(current, context, True, sort_map, var_map)
            btor2_prog += flatten_btor2_expr(btor2_current)
            btor2_prog.append(BtorConstraint(btor2_current))

        btor2_nids: dict[BtorNode, int] = {}
        cur_nid = 1
        for node in btor2_prog:
            if node in btor2_nids:
                node.nid = btor2_nids[node]
            else:
                node.nid = cur_nid
                btor2_nids[node] = cur_nid
                cur_nid += 1

        reduced_btor2_prog: list[BtorNode] = []
        for node in btor2_prog:
            if node in reduced_btor2_prog:
                continue
            reduced_btor2_prog.append(node)

        btor2_prog_list[sym] = reduced_btor2_prog

    return btor2_prog_list
    


def translate(il_prog: ILProgram) -> Optional[list[dict[str, list[BtorNode]]]]:
    """Translate `il_prog` to an equivalent set of Btor programs, labeled by query symbol.
    
    The strategy for translation is to sort check the input then construct a Btor program for each query (and targeted system) by:
    1) Constructing a mapping of ILSorts to BtorSorts for the target system
    2) Constructing a mapping of ILVars to BtorVars for the target system
    3) Translating the relevant model of the query 
    4) Translating the query

    1-3 recursively descend the IL of the program starting from the target system and traversing down through the system's init, trans, and inv expressions as well as any subsystems and 4 recursively descends the relevant attributes of the query.

    Note that the output programs will have input/output/local variables renamed based on the query, but all subsystem variables will remain as defined.
    """
    (well_sorted, context) = sort_check(il_prog)

    if not well_sorted:
        sys.stderr.write("Failed sort check\n")
        return None
    
    btor2_prog_list: list[dict[str, list[BtorNode]]] = []
    sort_map: SortMap = {}
    var_map: VarMap = {}
    enums: dict[str, int] = { sym:len(vals).bit_length() for sym,vals in context.declared_enum_sorts.items() }

    for check_system in il_prog.get_check_system_cmds():
        target_system = context.defined_systems[check_system.sys_symbol]

        build_sort_map_cmd(target_system, enums, sort_map)
        build_var_map_cmd(check_system, context, {}, sort_map, var_map)

        btor2_prog_list.append(ilchecksystem_to_btor2(check_system, context, sort_map, var_map))

    return btor2_prog_list


def main(
    input_path: Path, 
    output_path: Path, 
    pickle_path: Optional[Path]
) -> int:
    if not input_path.is_file():
        sys.stderr.write(f"Error: `{input_path}` is not a valid file.\n")
        return 1

    if output_path.is_file():
        sys.stderr.write(f"Error: `{output_path}` is a file.\n")
        return 1

    if not output_path.is_dir():
        output_path.mkdir()

    with open(input_path, "r") as file:
        if input_path.suffix == ".json":
            program = from_json(json.load(file))
        elif input_path.suffix == ".mcil":
            program = parse_il(file.read())
        else:
            sys.stderr.write(f"File format unsupported ({input_path.suffix})\n")
            return 1

    if not program:
        sys.stderr.write("Failed parsing\n")
        return 1

    output = translate(program)

    if output is None:
        sys.stderr.write("Failed translation\n")
        return 1

    check_system_index = 0
    for check_system in output:
        check_system_path = output_path / str(check_system_index)
        check_system_path.mkdir()

        for label, nodes in check_system.items():
            with open(check_system_path / f"{input_path.stem}.{label}.btor", "w") as f:
                f.write("\n".join([str(n) for n in nodes])) 
                f.write("\n")

            if pickle_path:
                with open(pickle_path, "wb") as f:
                    pickle.dump(nodes, f)
    
    return 0


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("input", help="source program to translate, should have either .json or .mcil extension")
    parser.add_argument("--output", help="path of directory to output BTOR2 files; defaults to input filename stem")
    parser.add_argument("--pickled-btor", help="path to output pickled btor output; will not emit by default")
    args = parser.parse_args()

    input_path = Path(args.input)
    output_path = Path(args.output) if args.output else Path(f"{input_path.stem}")
    pickle_path = Path(args.pickled_btor) if args.pickled_btor else None

    returncode = main(input_path, output_path, args.pickled_btor)
    sys.exit(returncode)
