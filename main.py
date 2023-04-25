from typing import Dict, List
from il import *
from btor2 import *


def ilsort_to_btor2(sort: ILSort) -> Btor2Sort:
    if sort.identifier.symbol == "Bool":
        return Btor2BitVec(1)
    elif sort.identifier.symbol == "BitVec" and isinstance(sort.identifier.indices[0], int):
        return Btor2BitVec(sort.identifier.indices[0])
    elif sort.identifier.symbol == "Array":
        return Btor2Array(ilsort_to_btor2(sort.sorts[0]), ilsort_to_btor2(sort.sorts[1]))
    else:
        raise NotImplementedError


def build_sort_map(expr: ILExpr, sort_map: Dict[ILSort, Btor2Sort]) -> None:
    
    def build_sort_map_util(cur: ILExpr) -> None:
        if not cur.sort in sort_map:
            sort_map[cur.sort] = ilsort_to_btor2(cur.sort)
    
    postorder_iterative(expr, build_sort_map_util)


def ilexpr_to_btor2(expr: ILExpr, sort_map: Dict[ILSort, Btor2Sort]) -> Btor2Expr:
    if isinstance(expr, ILInputVar):
        return Btor2InputVar(sort_map[expr.sort])
    elif isinstance(expr, ILOutputVar):
        return Btor2StateVar(sort_map[expr.sort])
    elif isinstance(expr, ILConstant):
        return Btor2Const(sort_map[expr.sort], expr.value)
    elif isinstance(expr, ILApply):
        if expr.function == "=":
            return Btor2Apply(sort_map[expr.sort], Btor2Operator.EQ, 
                              [ilexpr_to_btor2(expr.children[0], sort_map), 
                               ilexpr_to_btor2(expr.children[1], sort_map)])

    print(expr)
    raise NotImplementedError


def flatten_btor2_expr(expr: Btor2Expr) -> List[Btor2Expr]:
    out: List[Btor2Expr] = []

    def flatten_btor2_expr_util(cur: Btor2Expr) -> None:
        out.append(cur)
    
    postorder_iterative_btor2(expr, flatten_btor2_expr_util)
    return out


def translate(il_prog: ILProgram) -> List[Btor2Node]:
    btor2_prog: List[Btor2Node] = []
    sort_map: Dict[ILSort, Btor2Sort] = {}
    
    for cmd in il_prog.commands:
        if isinstance(cmd, ILDefineSystem):
            build_sort_map(cmd.init, sort_map)
            build_sort_map(cmd.trans, sort_map)
            build_sort_map(cmd.inv, sort_map)
        else:
            raise NotImplementedError
        
    btor2_prog += sort_map.values()
    

    for cmd in il_prog.commands:
        if isinstance(cmd, ILDefineSort):
            pass
        elif isinstance(cmd, ILDefineSystem):
            btor2_prog += flatten_btor2_expr(ilexpr_to_btor2(cmd.init, sort_map))
            btor2_prog += flatten_btor2_expr(ilexpr_to_btor2(cmd.trans, sort_map))
            btor2_prog += flatten_btor2_expr(ilexpr_to_btor2(cmd.inv, sort_map))
        elif isinstance(cmd, ILCheckSystem):
            pass
        else:
            raise NotImplementedError
        
    for i in range(0, len(btor2_prog)):
        node = btor2_prog[i]
        node.nid = i

    return btor2_prog


if __name__ == "__main__":
    bool_sort = ILSort(ILIdentifier("Bool", []), [])
    bv8_sort = ILSort(ILIdentifier("BitVec", [8]), [])

    in_var = ILInputVar("in", bv8_sort, False)
    out_var = ILOutputVar("out", bv8_sort, False)
    out_var_p = ILOutputVar("out", bv8_sort, True)

    init_cond = ILApply(ILIdentifier("=", []), [out_var, ILConstant(bv8_sort, 0)])
    init_cond.sort = bool_sort
    trans_cond = ILApply(ILIdentifier("=", []), [out_var_p, in_var])
    trans_cond.sort = bool_sort

    def_sys = ILDefineSystem(
        "s", 
        {}, 
        [],
        [],
        init_cond,
        trans_cond,
        ILConstant(bool_sort, True))

    prog = ILProgram([def_sys])

    output = translate(prog)
    
    for node in output:
        print(node)