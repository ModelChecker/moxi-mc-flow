from copy import copy
import readline
import sys
from typing import cast
from il import *
from btor2 import *
from parse import ILLexer, ILParser


USAGE: str = """Usage: main.py [input file]\n\tinput file: optional file for batch mode"""


ilfunc_map: dict[str, Btor2Operator] = {
    "=": Btor2Operator.EQ,
    "bvadd": Btor2Operator.ADD,
    "bvsmod": Btor2Operator.SMOD
}


def ilsort_to_btor2(sort: ILSort) -> Btor2Sort:
    if sort.identifier.symbol == "Bool":
        return Btor2BitVec(1)
    elif is_bv_sort(sort):
        return Btor2BitVec(sort.identifier.indices[0])
    elif sort.identifier.symbol == "Array":
        return Btor2Array(ilsort_to_btor2(sort.sorts[0]), ilsort_to_btor2(sort.sorts[1]))
    else:
        raise NotImplementedError


def build_sort_map_expr(expr: ILExpr) -> dict[ILSort, Btor2Sort]:
    """Iteratively recurse the expr AST and map each unique ILSort of each node to a new Btor2Sort."""
    sort_map: dict[ILSort, Btor2Sort] = {}

    def build_sort_map_util(cur: ILExpr):
        if not cur.sort in sort_map:
            sort_map[cur.sort] = ilsort_to_btor2(cur.sort)
    
    postorder_iterative(expr, build_sort_map_util)
    return sort_map


def build_sort_map_cmd(cmd: ILCommand) -> dict[ILSort, Btor2Sort]:
    sort_map: dict[ILSort, Btor2Sort] = {}

    if isinstance(cmd, ILDefineSystem):
        for subsystem in [s[1] for s in cmd.subsystems]:
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
    rename_map: dict[str, str],
    sort_map: dict[ILSort, Btor2Sort]
) -> dict[ILVar, Btor2Var|tuple[Btor2Var,Btor2Var,Btor2Var]]:
    """Iteratively recurse the expr AST and map each input ILVar to a single Btor2Input and each local/output var to a triple of Btor2States corresponding to that var's init, cur, and next values."""
    var_map: dict[ILVar, Btor2Var|tuple[Btor2Var,Btor2Var,Btor2Var]] = {}

    def build_var_map_util(cur: ILExpr):
        if isinstance(cur, ILVar) and not cur in var_map:
            if cur.symbol in rename_map:
                for k,v in var_map.items():
                    if rename_map[cur.symbol] == k.symbol:
                        var_map[cur] = v
                return

            symbol = rename_map[cur.symbol] if cur.symbol in rename_map else cur.symbol

            if isinstance(cur, ILInputVar):
                var_map[cur] = Btor2InputVar(sort_map[cur.sort], symbol)
            else: # output or local var
                var_map[cur] = (Btor2StateVar(sort_map[cur.sort], f"init_{symbol}"),
                                Btor2StateVar(sort_map[cur.sort], f"cur_{symbol}"),
                                Btor2StateVar(sort_map[cur.sort], f"next_{symbol}"))

    postorder_iterative(expr, build_var_map_util)
    return var_map


def build_var_map_cmd(
    cmd: ILCommand, 
    rename_map: dict[str, str],
    sort_map: dict[ILSort, Btor2Sort]
) -> dict[ILVar, Btor2Var|tuple[Btor2Var,Btor2Var,Btor2Var]]:
    var_map: dict[ILVar, Btor2Var|tuple[Btor2Var,Btor2Var,Btor2Var]] = {}

    if isinstance(cmd, ILDefineSystem):
        for subsystem in [s[1] for s in cmd.subsystems]:
            var_map.update(build_var_map_cmd(subsystem, rename_map, sort_map))

        var_map.update(build_var_map_expr(cmd.init, rename_map, sort_map))
        var_map.update(build_var_map_expr(cmd.trans, rename_map, sort_map))
        var_map.update(build_var_map_expr(cmd.inv, rename_map, sort_map))
    elif isinstance(cmd, ILCheckSystem):
        for assume in cmd.assumption.values():
            var_map.update(build_var_map_expr(assume, rename_map, sort_map))
        for fair in cmd.fairness.values():
            var_map.update(build_var_map_expr(fair, rename_map, sort_map))
        for reach in cmd.reachable.values():
            var_map.update(build_var_map_expr(reach, rename_map, sort_map))
        for current in cmd.current.values():
            var_map.update(build_var_map_expr(current, rename_map, sort_map))
    else:
        raise NotImplementedError

    return var_map


def ilexpr_to_btor2(
    expr: ILExpr, 
    is_init_expr: bool,
    sort_map: dict[ILSort, Btor2Sort],
    var_map: dict[ILVar, Btor2Var|tuple[Btor2Var,Btor2Var,Btor2Var]]
) -> Btor2Expr:
    if isinstance(expr, ILInputVar):
        return cast(Btor2Var, var_map[expr])
    elif isinstance(expr, ILOutputVar) or isinstance(expr, ILLocalVar):
        # We use "int(not is_init_expr)+int(expr.prime)" to compute the index in var_map:
        #   var_map[var][0] = init_var
        #   var_map[var][1] = cur_var
        #   var_map[var][2] = next_var
        return cast(tuple[Btor2Var,Btor2Var,Btor2Var], var_map[expr])[int(not is_init_expr)+int(expr.prime)]
    elif isinstance(expr, ILConstant):
        return Btor2Const(sort_map[expr.sort], expr.value)
    elif isinstance(expr, ILApply):
        return Btor2Apply(sort_map[expr.sort], ilfunc_map[expr.identifier.symbol], 
                        [ilexpr_to_btor2(c, is_init_expr, sort_map, var_map) for c in expr.children])

    raise NotImplementedError


def flatten_btor2_expr(expr: Btor2Expr) -> list[Btor2Expr]:
    out: list[Btor2Expr] = []

    def flatten_btor2_expr_util(cur: Btor2Expr):
        out.append(cur)
    
    postorder_iterative_btor2(expr, flatten_btor2_expr_util)
    return out


def ildefinesystem_to_btor2(
    sys: ILDefineSystem, 
    sort_map: dict[ILSort, Btor2Sort],
    var_map: dict[ILVar, Btor2Var|tuple[Btor2Var,Btor2Var,Btor2Var]]
) -> list[Btor2Node]:
    btor2_model: list[Btor2Node] = []

    btor2_model += [i for i in flatten_btor2_expr(ilexpr_to_btor2(sys.init, True, sort_map, var_map)) if not i in btor2_model]
    btor2_model.append(Btor2Constraint(btor2_model[len(btor2_model)-1]))

    for var in [v for v in var_map.values() if isinstance(v, tuple)]:
        btor2_model.append(Btor2Init(cast(Btor2StateVar, var[1]), var[0]))

    btor2_model += [i for i in flatten_btor2_expr(ilexpr_to_btor2(sys.trans, False, sort_map, var_map)) if not i in btor2_model]
    btor2_model.append(Btor2Constraint(btor2_model[len(btor2_model)-1]))

    for var in [v for v in var_map.values() if isinstance(v, tuple)]:
        btor2_model.append(Btor2Next(cast(Btor2StateVar, var[1]), var[2]))

    btor2_model += [i for i in flatten_btor2_expr(ilexpr_to_btor2(sys.inv, False, sort_map, var_map)) if not i in btor2_model]
    btor2_model.append(Btor2Constraint(btor2_model[len(btor2_model)-1]))

    return btor2_model
    


def translate(il_prog: ILProgram) -> dict[str, list[Btor2Node]]:
    """Translate `il_prog` to an equivalent set of Btor2 programs, labeled by query name.
    
    The strategy for translation is to sort check the input then construct a Btor2 program for each query (and targeted system) by:
    1) Constructing a mapping of ILSorts to Btor2Sorts for the target system
    2) Constructing a mapping of ILVars to Btor2Vars for the target system
    3) Translating the relevant model of the query 
    4) Translating the query

    1-3 recursively descend the AST of the program starting from the target system and traversing down through the system's init, trans, and inv expressions as well as any subsystems and 4 recursively descends the relevant attributes of the query.

    Note that the output programs will have input/output/local variables renamed based on the query, but all subsystem variables will remain as defined.
    """
    btor2_prog_list: dict[str, list[Btor2Node]] = {}
    sort_map: dict[ILSort, Btor2Sort] = {}
    var_map: dict[ILVar, Btor2Var|tuple[Btor2Var,Btor2Var,Btor2Var]] = {}

    (well_sorted, context) = sort_check(il_prog)

    if not well_sorted:
        print("Failed sort check")
        return {}

    for check_system in il_prog.get_check_systems():
        btor2_prog_list[check_system.sys_symbol] = []
        btor2_model = btor2_prog_list[check_system.sys_symbol]
        target_system = context.defined_systems[check_system.sys_symbol]

        sort_map = build_sort_map_cmd(target_system)
        # TODO: For now, this just outputs all mapped sorts so far, may want to be more selective about this
        btor2_model += sort_map.values()

        var_map = build_var_map_cmd(check_system, check_system.var_map, sort_map)
        var_map.update(build_var_map_cmd(target_system, check_system.var_map, sort_map))

        for val in var_map.values():
            if isinstance(val, Btor2Var):
                btor2_model.append(val)
            elif isinstance(val, tuple):
                btor2_model.append(val[0])
                btor2_model.append(val[1])
                btor2_model.append(val[2])
        
        for cmd in il_prog.commands:
            if isinstance(cmd, ILDefineSort):
                pass
            elif isinstance(cmd, ILDeclareConst):
                pass
            elif isinstance(cmd, ILDefineSystem):
                btor2_model += [i for i in flatten_btor2_expr(ilexpr_to_btor2(cmd.init, True, sort_map, var_map)) if not i in btor2_model]
                btor2_model.append(Btor2Constraint(btor2_model[len(btor2_model)-1]))

                for var in [v for v in var_map.values() if isinstance(v, tuple)]:
                    btor2_model.append(Btor2Init(cast(Btor2StateVar, var[1]), var[0]))

                btor2_model += [i for i in flatten_btor2_expr(ilexpr_to_btor2(cmd.trans, False, sort_map, var_map)) if not i in btor2_model]
                btor2_model.append(Btor2Constraint(btor2_model[len(btor2_model)-1]))

                for var in [v for v in var_map.values() if isinstance(v, tuple)]:
                    btor2_model.append(Btor2Next(cast(Btor2StateVar, var[1]), var[2]))

                btor2_model += [i for i in flatten_btor2_expr(ilexpr_to_btor2(cmd.inv, False, sort_map, var_map)) if not i in btor2_model]
                btor2_model.append(Btor2Constraint(btor2_model[len(btor2_model)-1]))
            elif isinstance(cmd, ILCheckSystem):
                for sym,query in cmd.query.items():
                    # shallow copy the prog since we don't want to lose sort_map/var_map
                    btor2_prog = copy(btor2_model)

                    for assume in [a[1] for a in cmd.assumption.items() if a[0] in query]:
                        btor2_prog += [i for i in flatten_btor2_expr(ilexpr_to_btor2(assume, False, sort_map, var_map)) if not i in btor2_prog]
                        btor2_prog.append(Btor2Constraint(btor2_prog[len(btor2_prog)-1]))

                    for reach in [r[1] for r in cmd.reachable.items() if r[0] in query]:
                        btor2_prog += [i for i in flatten_btor2_expr(ilexpr_to_btor2(reach, False, sort_map, var_map)) if not i in btor2_prog]
                        btor2_prog.append(Btor2Bad(btor2_prog[len(btor2_prog)-1]))
                    
                    for fair in [f[1] for f in cmd.fairness.items() if f[0] in query]:
                        btor2_prog += [i for i in flatten_btor2_expr(ilexpr_to_btor2(fair, False, sort_map, var_map)) if not i in btor2_prog]
                        btor2_prog.append(Btor2Fair(btor2_prog[len(btor2_prog)-1]))
                
                    for current in [c[1] for c in cmd.current.items() if c[0] in query]:
                        btor2_prog += [i for i in flatten_btor2_expr(ilexpr_to_btor2(current, True, sort_map, var_map)) if not i in btor2_prog]
                        btor2_prog.append(Btor2Constraint(btor2_prog[len(btor2_prog)-1]))

                    btor2_prog_list[sym] = btor2_prog
            else:
                raise NotImplementedError

        for btor2_var in [var for var in btor2_model if isinstance(var, Btor2Var)]:
            if btor2_var.name in check_system.var_map.values():
                pass
                

        for i in range(0, len(btor2_model)):
            node = btor2_model[i]
            node.nid = i+1

    return btor2_prog_list


def parse(input: str) -> ILProgram|None:
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
    
    for node in output["q"]:
        print(node)

    sys.exit(0)