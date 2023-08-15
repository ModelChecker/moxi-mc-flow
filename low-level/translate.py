from copy import copy
import sys
from typing import MappingView, TypeVar, cast

from il import *
from btor2 import *
from parse import ILLexer, ILParser


USAGE: str = """Usage: main.py <input file>"""

ilfunc_map: dict[str, Btor2Operator] = {
    "=": Btor2Operator.EQ,
    "!=": Btor2Operator.NEQ,
    "=>": Btor2Operator.IMPLIES,
    "iff": Btor2Operator.IFF,
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
}

VarMap = dict[ILVar, dict[ILSystemContext, Btor2Var|tuple[Btor2Var,Btor2Var,Btor2Var]]]
RenameMap = dict[ILVar, dict[ILSystemContext, tuple[ILVar, ILSystemContext]]]

def print_var_map(var_map: VarMap):
    for il_var, tmp in var_map.items():
        for sys_ctx, btor2_var in tmp.items():
            sys_ctx_str = "::".join(sys_ctx.get_scope_symbols())
            if isinstance(btor2_var, tuple):
                (init, cur, next) = btor2_var
                print(f"var_map[{il_var}][{sys_ctx_str}] = ({id(init)}, {id(cur)}, {id(next)})")
            else:
                print(f"var_map[{il_var}][{sys_ctx_str}] = {id(btor2_var)}")


def print_rename_map(rename_map: RenameMap):
    for (var,d) in rename_map.items():
        for (ctx,tup) in d.items():
            target_var, target_ctx = tup
            scope_1 = "::".join(ctx.get_scope_symbols())
            scope_2 = "::".join(target_ctx.get_scope_symbols())
            print(f"({var}, {scope_1}) : ({target_var}, {scope_2})")


def ilsort_to_btor2(sort: ILSort) -> Btor2Sort:
    if is_bool_sort(sort):
        return Btor2BitVec(1)
    elif is_bv_sort(sort):
        return Btor2BitVec(sort.identifier.indices[0])
    elif sort.identifier.symbol == "Array":
        return Btor2Array(ilsort_to_btor2(sort.sorts[0]), ilsort_to_btor2(sort.sorts[1]))
    else:
        raise NotImplementedError


def build_sort_map_expr(expr: ILExpr) -> dict[ILSort, Btor2Sort]:
    """Iteratively recurse the expr IL and map each unique ILSort of each node to a new Btor2Sort."""
    sort_map: dict[ILSort, Btor2Sort] = {}

    def build_sort_map_util(cur: ILExpr):
        if cur.sort not in sort_map:
            sort_map[cur.sort] = ilsort_to_btor2(cur.sort)
    
    postorder_iterative(expr, build_sort_map_util)
    return sort_map


def build_sort_map_cmd(cmd: ILCommand) -> dict[ILSort, Btor2Sort]:
    sort_map: dict[ILSort, Btor2Sort] = {}

    if isinstance(cmd, ILDefineSystem):
        for subsystem in cmd.subsystems.values():
            sort_map.update(build_sort_map_cmd(subsystem))

        sort_map.update(build_sort_map_expr(cmd.init))
        sort_map.update(build_sort_map_expr(cmd.trans))
        sort_map.update(build_sort_map_expr(cmd.inv))
    elif isinstance(cmd, ILCheckSystem):
        for assume in cmd.assumption.values():
            sort_map.update(build_sort_map_expr(assume))
        for fair in cmd.fairness.values():
            sort_map.update(build_sort_map_expr(fair))
        for reach in cmd.reachable.values():
            sort_map.update(build_sort_map_expr(reach))
        for current in cmd.current.values():
            sort_map.update(build_sort_map_expr(current))
    else:
        raise NotImplementedError

    return sort_map


def build_var_map_expr(
    expr: ILExpr,
    context: ILContext,
    rename_map: RenameMap,
    sort_map: dict[ILSort, Btor2Sort],
    var_map: VarMap):
    """Iteratively recurse the expr IL and map each input ILVar to a single Btor2Input and each local/output var to a triple of Btor2States corresponding to that var's init, cur, and next values."""
    def build_var_map_util(expr: ILExpr):
        system_context = context.system_context
        if isinstance(expr, ILVar) and ((expr not in var_map) or (system_context not in var_map[expr])):
            cur = expr

            while cur in rename_map and system_context in rename_map[cur]:
                (cur, system_context) = rename_map[cur][system_context]

            symbol = "::".join(system_context.get_scope_symbols() + [cur.symbol])

            if expr not in var_map:
                var_map[expr] = {}

            if expr.var_type == ILVarType.INPUT:
                var_map[expr][context.system_context.copy()] = Btor2InputVar(sort_map[cur.sort], symbol)
            else: # output or local var
                var_map[expr][context.system_context.copy()] = (Btor2StateVar(sort_map[cur.sort], f"{symbol}::init"),
                                                 Btor2StateVar(sort_map[cur.sort], f"{symbol}::cur"),
                                                 Btor2StateVar(sort_map[cur.sort], f"{symbol}::next"))

    postorder_iterative(expr, build_var_map_util)


def build_var_map_cmd(
    cmd: ILCommand, 
    context: ILContext,
    rename_map: RenameMap,
    sort_map: dict[ILSort, Btor2Sort],
    var_map: VarMap):
    """Update var_map to map all ILVar instances to Btor2Vars"""
    if isinstance(cmd, ILDefineSystem):
        for (subsys_symbol, subsystem) in cmd.subsystems.items():
            signature: list[ILVar] = []
            for symbol in cmd.subsystem_signatures[subsys_symbol][1]:
                for var in cmd.input + cmd.output + cmd.local:
                    if var.symbol == symbol:
                        signature.append(var)

            target_signature = subsystem.input + subsystem.output
        
            target_context = context.system_context.copy() # need to copy for now
            target_context.push((subsys_symbol, subsystem))

            for cmd_var,target_var in zip(signature, target_signature):
                if target_var not in rename_map:
                    rename_map[target_var] = {}
                rename_map[target_var][target_context] = (cmd_var, context.system_context.copy())
            
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
        signature = cmd.input + cmd.output + cmd.local
        target_signature = target_system.input + target_system.output + target_system.local
    
        target_context = context.system_context.copy() # need to copy for now
        target_context.push((target_system.symbol, target_system))

        for cmd_var,target_var in zip(signature, target_signature):
            if target_var not in rename_map:
                rename_map[target_var] = {}
            rename_map[target_var][target_context] = (cmd_var, context.system_context.copy())

        context.system_context.push((cmd.sys_symbol, target_system))
        build_var_map_cmd(target_system, context, rename_map, sort_map, var_map)        
        context.system_context.pop()
    else:
        raise NotImplementedError


def ilexpr_to_btor2(
    expr: ILExpr, 
    context: ILContext,
    is_init_expr: bool,
    sort_map: dict[ILSort, Btor2Sort],
    var_map: VarMap
) -> Btor2Expr:
    if isinstance(expr, ILVar) and expr.var_type == ILVarType.INPUT:
        return cast(Btor2Var, var_map[expr][context.system_context])
    elif isinstance(expr, ILVar):
        # We use "int(not is_init_expr)+int(expr.prime)" to compute the index in var_map:
        #   var_map[var] = (init, cur, next)
        return cast(tuple[Btor2Var,Btor2Var,Btor2Var], var_map[expr][context.system_context])[int(not is_init_expr)+int(expr.prime)]
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
            

def ilsubsystem_to_btor2(
    subsystem: ILDefineSystem, 
    context: ILContext,
    sort_map: dict[ILSort, Btor2Sort],
    var_map: VarMap
) -> list[Btor2Node]:
    btor2_model: list[Btor2Node] = []

    # Note: var_map may have repeat values (i.e., renamed variables point to same Btor2 variables)
    for val in set([v.values() for v in var_map.values()]):
        if isinstance(val, Btor2Var):
            btor2_model.append(val)
        elif isinstance(val, tuple):
            btor2_model.append(val[0])
            btor2_model.append(val[1])
            btor2_model.append(val[2])

    btor2_init = ilexpr_to_btor2(subsystem.init, context, True, sort_map, var_map)
    btor2_model += flatten_btor2_expr(btor2_init)
    btor2_model.append(Btor2Constraint(btor2_init))

    for var in [v for v in [v.values() for v in var_map.values()] if isinstance(v, tuple)]:
        btor2_model.append(Btor2Init(cast(Btor2StateVar, var[1]), var[0]))

    btor2_trans = ilexpr_to_btor2(subsystem.trans, context, False, sort_map, var_map)
    btor2_model += flatten_btor2_expr(btor2_trans)
    btor2_model.append(Btor2Constraint(btor2_trans))

    for var in [v for v in [v.values() for v in var_map.values()] if isinstance(v, tuple)]:
        btor2_model.append(Btor2Next(cast(Btor2StateVar, var[1]), var[2]))

    btor2_inv = ilexpr_to_btor2(subsystem.inv, context, False, sort_map, var_map)
    btor2_model += flatten_btor2_expr(btor2_inv)
    btor2_model.append(Btor2Constraint(btor2_inv))

    return btor2_model


def ilsystem_to_btor2(
    system: ILDefineSystem, 
    context: ILContext,
    sort_map: dict[ILSort, Btor2Sort],
    var_map: VarMap
) -> list[Btor2Node]:
    btor2_model: list[Btor2Node] = []

    for sort in sort_map.values():
        btor2_model.append(sort)

    # Note: var_map may have repeat values (i.e., renamed variables point to same Btor2 variables)
    for val in set([v.values() for v in var_map.values()]):
        if isinstance(val, Btor2Var):
            btor2_model.append(val)
        elif isinstance(val, tuple):
            btor2_model.append(val[0])
            btor2_model.append(val[1])
            btor2_model.append(val[2])

    btor2_init = ilexpr_to_btor2(system.init, context, True, sort_map, var_map)
    btor2_model += flatten_btor2_expr(btor2_init)
    btor2_model.append(Btor2Constraint(btor2_init))

    for var in [v for v in [v.values() for v in var_map.values()] if isinstance(v, tuple)]:
        btor2_model.append(Btor2Init(cast(Btor2StateVar, var[1]), var[0]))

    btor2_trans = ilexpr_to_btor2(system.trans, context, False, sort_map, var_map)
    btor2_model += flatten_btor2_expr(btor2_trans)
    btor2_model.append(Btor2Constraint(btor2_trans))

    for var in [v for v in [v.values() for v in var_map.values()] if isinstance(v, tuple)]:
        btor2_model.append(Btor2Next(cast(Btor2StateVar, var[1]), var[2]))

    btor2_inv = ilexpr_to_btor2(system.inv, context, False, sort_map, var_map)
    btor2_model += flatten_btor2_expr(btor2_inv)
    btor2_model.append(Btor2Constraint(btor2_inv))

    for symbol,subsystem in system.subsystems.items():
        context.system_context.push((symbol, subsystem))
        btor2_model += ilsystem_to_btor2(subsystem, context, sort_map, var_map)
        context.system_context.pop()

    return btor2_model


def ilchecksystem_to_btor2(
    check: ILCheckSystem, 
    context: ILContext,
    sort_map: dict[ILSort, Btor2Sort],
    var_map: VarMap,
) -> dict[str, list[Btor2Node]]:
    """A check_system command can have many queries: each query will have the same target system but may correspond to different models of that system. First, we construct that reference BTOR2 model, then for each query we generate a new BTOR2 program with the reference model as a prefix and query as a suffix."""
    btor2_prog_list: dict[str, list[Btor2Node]] = {}
    btor2_model: list[Btor2Node] = []

    context.system_context.push((check.sys_symbol, context.defined_systems[check.sys_symbol]))
    btor2_model += ilsystem_to_btor2(context.defined_systems[check.sys_symbol], context, sort_map, var_map)
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
    btor2_prog_list: dict[str, list[Btor2Node]] = {}
    sort_map: dict[ILSort, Btor2Sort] = {}
    var_map: VarMap = {}

    (well_sorted, context) = sort_check(il_prog)

    if not well_sorted:
        print("Failed sort check")
        return {}

    for check_system in il_prog.get_check_system_cmds():
        btor2_prog_list[check_system.sys_symbol] = []
        target_system = context.defined_systems[check_system.sys_symbol]

        sort_map = build_sort_map_cmd(target_system)
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

    with open(sys.argv[1],"r") as file:
        program = parse(file.read())

    if not program:
        print("Failed parsing")
        sys.exit(1)

    output = translate(program)
    
    with open("test.btor", "w") as f:
        for label,nodes in output.items():
            # f.write(f"; {label}\n")
            for n in nodes:
                f.write(f"{n}\n")

    sys.exit(0)