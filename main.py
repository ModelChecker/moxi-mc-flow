import sys
from typing import cast
from il import *
from btor2 import *
from parse import ILLexer, ILParser


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


def build_sort_map(expr: ILExpr) -> dict[ILSort, Btor2Sort]:
    """Iteratively recurse the expr AST and map each unique ILSort of each node to a new Btor2Sort."""
    sort_map: dict[ILSort, Btor2Sort] = {}

    def build_sort_map_util(cur: ILExpr):
        if not cur.sort in sort_map:
            sort_map[cur.sort] = ilsort_to_btor2(cur.sort)
    
    postorder_iterative(expr, build_sort_map_util)
    return sort_map


def build_var_map(
    expr: ILExpr, 
    sort_map: dict[ILSort, Btor2Sort]
) -> dict[ILVar, Btor2Var|tuple[Btor2Var,Btor2Var,Btor2Var]]:
    """Iteratively recurse the expr AST and map each input ILVar to a single Btor2Input and each local/output var to a triple of Btor2States corresponding to that var's init, cur, and next values."""
    var_map: dict[ILVar, Btor2Var|tuple[Btor2Var,Btor2Var,Btor2Var]] = {}

    def build_var_map_util(cur: ILExpr):
        if isinstance(cur, ILVar) and not cur in var_map:
            if isinstance(cur, ILInputVar):
                var_map[cur] = Btor2InputVar(sort_map[cur.sort], cur.symbol)
            else: # output or local var
                var_map[cur] = (Btor2StateVar(sort_map[cur.sort], f"init_{cur.symbol}"),
                                Btor2StateVar(sort_map[cur.sort], f"cur_{cur.symbol}"),
                                Btor2StateVar(sort_map[cur.sort], f"next_{cur.symbol}"))

    postorder_iterative(expr, build_var_map_util)
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
        # var_map[var][0] = init_var
        # var_map[var][1] = cur_var
        # var_map[var][2] = next_var
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


def translate(il_prog: ILProgram) -> list[Btor2Node]:
    btor2_prog: list[Btor2Node] = []
    sort_map: dict[ILSort, Btor2Sort] = {}
    var_map: dict[ILVar, Btor2Var|tuple[Btor2Var,Btor2Var,Btor2Var]] = {}

    if not sort_check(il_prog):
        print("Failed sort check")
        return []
    
    for cmd in il_prog.commands:
        if isinstance(cmd, ILDeclareConst):
            pass
        elif isinstance(cmd, ILDefineSystem):
            sort_map.update(build_sort_map(cmd.init))
            sort_map.update(build_sort_map(cmd.trans))
            sort_map.update(build_sort_map(cmd.inv))
        else:
            raise NotImplementedError
        
    btor2_prog += sort_map.values()
    
    for cmd in il_prog.commands:
        if isinstance(cmd, ILDeclareConst):
            pass
        elif isinstance(cmd, ILDefineSystem):
            var_map.update(build_var_map(cmd.init, sort_map))
            var_map.update(build_var_map(cmd.trans, sort_map))
            var_map.update(build_var_map(cmd.inv, sort_map))
        else:
            raise NotImplementedError

    for val in var_map.values():
        if isinstance(val, Btor2Var):
            btor2_prog.append(val)
        elif isinstance(val, tuple):
            btor2_prog.append(val[0])
            btor2_prog.append(val[1])
            btor2_prog.append(val[2])
    
    for cmd in il_prog.commands:
        if isinstance(cmd, ILDefineSort):
            pass
        elif isinstance(cmd, ILDeclareConst):
            pass
        elif isinstance(cmd, ILDefineSystem):
            btor2_prog += [i for i in flatten_btor2_expr(ilexpr_to_btor2(cmd.init, True, sort_map, var_map)) if not i in btor2_prog]
            btor2_prog.append(Btor2Constraint(btor2_prog[len(btor2_prog)-1]))

            for var in [v for v in var_map.values() if isinstance(v, tuple)]:
                btor2_prog.append(Btor2Init(cast(Btor2StateVar, var[1]), var[0]))

            btor2_prog += [i for i in flatten_btor2_expr(ilexpr_to_btor2(cmd.trans, False, sort_map, var_map)) if not i in btor2_prog]
            btor2_prog.append(Btor2Constraint(btor2_prog[len(btor2_prog)-1]))

            for var in [v for v in var_map.values() if isinstance(v, tuple)]:
                btor2_prog.append(Btor2Next(cast(Btor2StateVar, var[1]), var[2]))

            btor2_prog += [i for i in flatten_btor2_expr(ilexpr_to_btor2(cmd.inv, False, sort_map, var_map)) if not i in btor2_prog]
            btor2_prog.append(Btor2Constraint(btor2_prog[len(btor2_prog)-1]))
        elif isinstance(cmd, ILCheckSystem):
            pass
        else:
            raise NotImplementedError
        
    for i in range(0, len(btor2_prog)):
        node = btor2_prog[i]
        node.nid = i+1

    return btor2_prog


def parse(input: str) -> ILProgram|None:
    """Parse contents of input and returns corresponding program on success, else returns None."""
    lexer: ILLexer = ILLexer()
    parser: ILParser = ILParser()
    cmds: list[ILCommand] = parser.parse(lexer.tokenize(input))
    return ILProgram(cmds)


if __name__ == "__main__":

    with open(sys.argv[1],"r") as file:
        program = parse(file.read())

    if not program:
        print("Failed parsing")
        sys.exit(1)

    print("------------------")

    output = translate(program)
    
    for node in output:
        print(node)

    sys.exit(0)