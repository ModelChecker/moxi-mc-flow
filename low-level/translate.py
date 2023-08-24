from copy import copy
import json
from pathlib import Path
import sys
from typing import cast

from il import *
from btor2 import *
from parse import ILLexer, ILParser


USAGE: str = """Usage: main.py <input file>"""

ilfunc_map: dict[str, Btor2Operator] = {
    "=": Btor2Operator.EQ,
    "!=": Btor2Operator.NEQ,
    "=>": Btor2Operator.IMPLIES,
    "iff": Btor2Operator.IFF,
    "not": Btor2Operator.NOT,
    "and": Btor2Operator.AND,
    "or": Btor2Operator.OR,
    "xor": Btor2Operator.XOR,
    "ite": Btor2Operator.ITE,
    "concat": Btor2Operator.CONCAT,
    "extract": Btor2Operator.SLICE,
    "zero_extend": Btor2Operator.UEXT,
    "sign_extend": Btor2Operator.SEXT,
    "rotate_left": Btor2Operator.ROL,
    "rotate_right": Btor2Operator.ROR,
    "bvshl": Btor2Operator.SLL,
    "bvlshr": Btor2Operator.SRL,
    "bvashr": Btor2Operator.SRA,
    "bvnot": Btor2Operator.NOT,
    "bvneg": Btor2Operator.NEG,
    "bvand": Btor2Operator.AND,
    "bvnand": Btor2Operator.NAND,
    "bvor": Btor2Operator.OR,
    "bvnor": Btor2Operator.NOR,
    "bvxor": Btor2Operator.XOR,
    "bvxnor": Btor2Operator.XNOR,
    "bvadd": Btor2Operator.ADD,
    "bvsub": Btor2Operator.SUB,
    "bvmul": Btor2Operator.MUL,
    "bvudiv": Btor2Operator.UDIV,
    "bvsdiv": Btor2Operator.SDIV,
    "bvurem": Btor2Operator.UREM,
    "bvsrem": Btor2Operator.SREM,
    "bvsmod": Btor2Operator.SMOD,
    "bvult": Btor2Operator.ULT,
    "bvule": Btor2Operator.ULTE,
    "bvugt": Btor2Operator.UGT,
    "bvuge": Btor2Operator.UGTE,
    "bvslt": Btor2Operator.SLT,
    "bvsle": Btor2Operator.SLTE,
    "bvsgt": Btor2Operator.SGT,
    "bvsge": Btor2Operator.SGTE,
    "reduce_and": Btor2Operator.REDAND,
    "reduce_or": Btor2Operator.REDOR,
    "reduce_xor": Btor2Operator.REDXOR,
    "select": Btor2Operator.READ,
    "store": Btor2Operator.WRITE 
}

# A SortMap maps ILSorts to BTOR2 sorts
SortMap = dict[ILSort, Btor2Sort]

# A VarMap maps variables in a system context to BTOR2 variables. BTOR2 variables are tuples by default (to handle
# initial, current, and next values) for output and state variables, whereas inputs are just a single variable.
VarMap = dict[tuple[ILVar, ILSystemContext], tuple[Btor2Var,Btor2Var,Btor2Var] | Btor2Var]

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


def ilsort_to_btor2(sort: ILSort, enums: dict[str, int], sort_map: SortMap) -> Btor2Sort:
    if sort in sort_map:
        return sort_map[sort]
    elif is_bool_sort(sort):
        return Btor2BitVec(1)
    elif is_bitvec_sort(sort):
        return Btor2BitVec(sort.identifier.indices[0])
    elif sort.identifier.symbol == "Array":
        return Btor2Array(ilsort_to_btor2(sort.parameters[0], enums, sort_map), 
                          ilsort_to_btor2(sort.parameters[1], enums, sort_map))
    elif sort.identifier.symbol in enums:
        return Btor2BitVec(enums[sort.identifier.symbol])
    else:
        raise NotImplementedError


def build_sort_map_expr(expr: ILExpr, enums: dict[str, int], sort_map: SortMap) -> SortMap:
    """Iteratively recurse the expr IL and map each unique ILSort of each node to a new Btor2Sort."""
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
    """Iteratively recurse the expr IL and map each input ILVar to a single Btor2Input and each local/output var to a
    triple of Btor2States corresponding to that var's init, cur, and next values."""
    def build_var_map_util(expr: ILExpr):
        if isinstance(expr, ILVar) and (expr, context.system_context) not in var_map:
            var, system_context = rename_lookup(expr, context.system_context, rename_map)

            symbol = "::".join(system_context.get_scope_symbols() + [var.symbol])

            # note: those system context copies only copy the pointers + they are only as big as the subsystems are deep
            if var.var_type == ILVarType.INPUT:
                var_map[(expr, context.system_context.copy())] = Btor2InputVar(sort_map[var.sort], symbol)
            elif var.var_type == ILVarType.OUTPUT or var.var_type == ILVarType.LOCAL:
                var_map[(expr, context.system_context.copy())] = (Btor2StateVar(sort_map[var.sort], f"{symbol}.init"),
                                                 Btor2StateVar(sort_map[var.sort], f"{symbol}.cur"),
                                                 Btor2StateVar(sort_map[var.sort], f"{symbol}.next"))

    postorder_iterative(expr, build_var_map_util)


def build_var_map_cmd(
    cmd: ILCommand, 
    context: ILContext,
    rename_map: RenameMap,
    sort_map: SortMap,
    var_map: VarMap):
    """Update var_map to map all ILVar instances to Btor2Vars"""
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
) -> Btor2Expr:
    if isinstance(expr, ILVar) and isinstance(var_map[(expr, context.system_context)], tuple):
        # We use "int(not is_init_expr) + int(expr.prime)" to compute the index in var_map tuple:
        #   var_map[var] = (init, cur, next)
        idx = int(not is_init_expr) + (expr.prime)
        return cast(tuple[Btor2Var,Btor2Var,Btor2Var], var_map[(expr, context.system_context)])[idx]
    elif isinstance(expr, ILVar):
        return cast(Btor2Var, var_map[(expr, context.system_context)])
    elif isinstance(expr, ILConstant) and expr.sort.identifier.symbol in context.declared_enum_sorts:
        value = context.declared_enum_sorts[expr.sort.identifier.symbol].index(expr.value)
        return Btor2Const(sort_map[expr.sort], value)
    elif isinstance(expr, ILConstant):
        return Btor2Const(sort_map[expr.sort], expr.value)
    elif isinstance(expr, ILApply):
        if len(expr.children) > 3:
            raise NotImplementedError

        tmp_children = copy(expr.children) + ([None] * (3 - len(expr.children)))
        (arg1, arg2, arg3) = tuple(tmp_children)

        btor2_args = (ilexpr_to_btor2(arg1, context, is_init_expr, sort_map, var_map) if arg1 else None,
                      ilexpr_to_btor2(arg2, context, is_init_expr, sort_map, var_map) if arg2 else None,
                      ilexpr_to_btor2(arg3, context, is_init_expr, sort_map, var_map) if arg3 else None)
        return Btor2Apply(sort_map[expr.sort], ilfunc_map[expr.identifier.symbol], btor2_args)

    raise NotImplementedError


def flatten_btor2_expr(expr: Btor2Expr) -> list[Btor2Expr]:
    out: list[Btor2Expr] = []

    def flatten_btor2_expr_util(cur: Btor2Expr):
        out.append(cur)
    
    postorder_iterative_btor2(expr, flatten_btor2_expr_util)
    return out


def ilsystem_to_btor2(
    btor2_model: list[Btor2Node],
    system: ILDefineSystem, 
    context: ILContext,
    sort_map: SortMap,
    var_map: VarMap):
    for symbol,subsystem in system.subsystems.items():
        context.system_context.push((symbol, subsystem))
        # btor2_model[-1].set_comment(f"begin {system.symbol}::{symbol}")
        ilsystem_to_btor2(btor2_model, subsystem, context, sort_map, var_map)
        # btor2_model[-1].set_comment(f"end {system.symbol}::{symbol}")
        context.system_context.pop()

    btor2_init = ilexpr_to_btor2(system.init, context, True, sort_map, var_map)
    btor2_model += flatten_btor2_expr(btor2_init)
    btor2_model.append(Btor2Constraint(btor2_init))
    btor2_model[-1].set_comment(f"init {system.symbol}")

    for btor2_var in [v for v in var_map.values() if isinstance(v, tuple)]:
        (init, cur, next) = btor2_var
        btor2_model.append(Btor2Init(cast(Btor2StateVar, cur), init))

    btor2_trans = ilexpr_to_btor2(system.trans, context, False, sort_map, var_map)
    btor2_model += flatten_btor2_expr(btor2_trans)
    btor2_model.append(Btor2Constraint(btor2_trans))
    btor2_model[-1].set_comment(f"trans {system.symbol}")

    for btor2_var in [v for v in var_map.values() if isinstance(v, tuple)]:
        (init, cur, next) = btor2_var
        btor2_model.append(Btor2Next(cast(Btor2StateVar, cur), next))

    btor2_inv = ilexpr_to_btor2(system.inv, context, False, sort_map, var_map)
    btor2_model += flatten_btor2_expr(btor2_inv)
    btor2_model.append(Btor2Constraint(btor2_inv))
    btor2_model[-1].set_comment(f"inv {system.symbol}")


def ilchecksystem_to_btor2(
    check: ILCheckSystem, 
    context: ILContext,
    sort_map: SortMap,
    var_map: VarMap,
) -> dict[str, list[Btor2Node]]:
    """A check_system command can have many queries: each query will have the same target system but may correspond to different models of that system. First, we construct that reference BTOR2 model, then for each query we generate a new BTOR2 program with the reference model as a prefix and query as a suffix."""
    btor2_prog_list: dict[str, list[Btor2Node]] = {}
    btor2_model: list[Btor2Node] = []

    for sort in sort_map.values():
        btor2_model.append(sort)

    # Note: var_map may have repeat values (i.e., renamed variables point to same Btor2 variables)
    for btor2_var in set(var_map.values()):
        if isinstance(btor2_var, Btor2Var):
            btor2_model.append(btor2_var)
        elif isinstance(btor2_var, tuple):
            (init, cur, next) = btor2_var
            btor2_model.append(init)
            btor2_model.append(cur)
            btor2_model.append(next)

    context.system_context.push((check.sys_symbol, context.defined_systems[check.sys_symbol]))
    ilsystem_to_btor2(btor2_model, context.defined_systems[check.sys_symbol], context, sort_map, var_map)
    context.system_context.pop()

    for sym,query in check.query.items():
        # shallow copy the prog since we don't want to lose sort_map/var_map
        btor2_prog = copy(btor2_model)

        for assume in [a[1] for a in check.assumption.items() if a[0] in query]:
            btor2_assume = ilexpr_to_btor2(assume, context, False, sort_map, var_map)
            btor2_prog += flatten_btor2_expr(btor2_assume)
            btor2_prog.append(Btor2Constraint(btor2_assume))

        for reach in [r[1] for r in check.reachable.items() if r[0] in query]:
            btor2_reach = ilexpr_to_btor2(reach, context, False, sort_map, var_map)
            btor2_prog += flatten_btor2_expr(btor2_reach)
            btor2_prog.append(Btor2Bad(btor2_reach))
        
        for fair in [f[1] for f in check.fairness.items() if f[0] in query]:
            btor2_fair = ilexpr_to_btor2(fair, context, False, sort_map, var_map)
            btor2_prog += flatten_btor2_expr(btor2_fair)
            btor2_prog.append(Btor2Fair(btor2_fair))
    
        for current in [c[1] for c in check.current.items() if c[0] in query]:
            btor2_current = ilexpr_to_btor2(current, context, True, sort_map, var_map)
            btor2_prog += flatten_btor2_expr(btor2_current)
            btor2_prog.append(Btor2Constraint(btor2_current))

        btor2_nids: dict[Btor2Node, int] = {}
        cur_nid = 1
        for node in btor2_prog:
            if node in btor2_nids:
                node.nid = btor2_nids[node]
            else:
                node.nid = cur_nid
                btor2_nids[node] = cur_nid
                cur_nid += 1

        reduced_btor2_prog: list[Btor2Node] = []
        for node in btor2_prog:
            if node in reduced_btor2_prog:
                continue
            reduced_btor2_prog.append(node)

        btor2_prog_list[sym] = reduced_btor2_prog

    return btor2_prog_list
    


def translate(il_prog: ILProgram) -> dict[str, list[Btor2Node]]:
    """Translate `il_prog` to an equivalent set of Btor2 programs, labeled by query name.
    
    The strategy for translation is to sort check the input then construct a Btor2 program for each query (and targeted system) by:
    1) Constructing a mapping of ILSorts to Btor2Sorts for the target system
    2) Constructing a mapping of ILVars to Btor2Vars for the target system
    3) Translating the relevant model of the query 
    4) Translating the query

    1-3 recursively descend the IL of the program starting from the target system and traversing down through the system's init, trans, and inv expressions as well as any subsystems and 4 recursively descends the relevant attributes of the query.

    Note that the output programs will have input/output/local variables renamed based on the query, but all subsystem variables will remain as defined.
    """
    (well_sorted, context) = sort_check(il_prog)

    if not well_sorted:
        print("Failed sort check")
        return {}
    
    btor2_prog_list: dict[str, list[Btor2Node]] = {}
    sort_map: SortMap = {}
    var_map: VarMap = {}
    enums: dict[str, int] = { sym:len(vals).bit_length() for sym,vals in context.declared_enum_sorts.items() }

    for check_system in il_prog.get_check_system_cmds():
        btor2_prog_list[check_system.sys_symbol] = []
        target_system = context.defined_systems[check_system.sys_symbol]

        build_sort_map_cmd(target_system, enums, sort_map)
        build_var_map_cmd(check_system, context, {}, sort_map, var_map)

        btor2_prog_list.update(ilchecksystem_to_btor2(check_system, context, sort_map, var_map))

    return btor2_prog_list


def parse(input: str) -> Optional[ILProgram]:
    """Parse contents of input and returns corresponding program on success, else returns None."""
    lexer: ILLexer = ILLexer()
    parser: ILParser = ILParser()
    cmds = parser.parse(lexer.tokenize(input))
    return ILProgram(cmds) if not cmds == None else None


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print(USAGE)
        sys.exit(1)

    filename = Path(sys.argv[1])

    if not filename.is_file():
        print(f"Error: `{filename}` is not a valid file.")
        sys.exit(1)

    with open(filename,"r") as file:
        if filename.suffix == ".json":
            program = from_json(json.load(file))
        else:
            program = parse(file.read())

    if not program:
        print("Failed parsing")
        sys.exit(1)

    output = translate(program)
    
    with open(f"{filename.stem}.btor", "w") as f:
        for label,nodes in output.items():
            # f.write(f"; {label}\n")
            for n in nodes:
                f.write(f"{n}\n")

    sys.exit(0)