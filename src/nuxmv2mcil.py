from pathlib import Path
from typing import Tuple, cast

from .util import logger
from .preprocess_nuxmv import preprocess
from .parse_nuxmv import parse, parse
from .nuxmv import *
from .mcil import *

FILE_NAME = Path(__file__).name

# TODO: Simplify expression handling with function map
# fn_map: dict[tuple[str, OpType], str] = {
#     ("&", OpType.BOOL_SORT): "and", ("&", OpType.BITVEC_SORT): "bvand",
#     ("|", OpType.BOOL_SORT): "or", ("|", OpType.BITVEC_SORT): "bvor",
#     ("xor", OpType.BOOL_SORT): "xor", ("xor", OpType.BITVEC_SORT): "bvxor",
#     # ("xnor", MCIL_BOOL_SORT): "xnor", ("xnor", MCIL_BITVEC_SORT): "bvxor",
#     ("->", OpType.BOOL_SORT): "=>",
#     ("!=", OpType.BOOL_SORT): "distinct",
#     (">=", OpType.INT_SORT): ">=", (">=", OpType.BITVEC_SORT): "bvuge",
#     ("<=", OpType.INT_SORT): "<=", ("<=", OpType.BITVEC_SORT): "bvule",
#     ("<", OpType.INT_SORT): "<", ("<", OpType.BITVEC_SORT): "bvult",
#     (">", OpType.INT_SORT): ">", (">", OpType.BITVEC_SORT): "bvugt",
#     ("+", OpType.INT_SORT): "+", ("+", OpType.BITVEC_SORT): "bvadd",
#     ("*", OpType.INT_SORT): "*", ("*", OpType.BITVEC_SORT): "bvmul",
# }

def translate_type(xmv_type: XMVType, xmv_context: XMVContext) -> MCILSort:
    match xmv_type:
        case XMVBoolean():
            return MCIL_BOOL_SORT
        case XMVInteger():
            return MCIL_INT_SORT
        case XMVReal():
            raise ValueError("nuXmv `real` type not supported in the IL (yet?)")
        case XMVClock():
            raise ValueError("nuXmv `clock` type not supported in the IL (yet?)")
        case XMVWord(width=w):
            return MCIL_BITVEC_SORT(int(w))
        case XMVArray(type=t):
            return MCIL_ARRAY_SORT(MCIL_INT_SORT, translate_type(t, xmv_context))
        case XMVWordArray(word_length=wl, type=t):
            return MCIL_ARRAY_SORT(MCIL_BITVEC_SORT(int(wl)), translate_type(t, xmv_context))
        case XMVModuleType():
            raise ValueError(f"Cannot translate type {xmv_type}")
        case XMVEnumeration():
            if xmv_type.is_integer():
                return MCIL_INT_SORT
            
            sums = xmv_type.summands
            lsums = list(sums)
            slsums = [str(s) for s in lsums]

            return MCIL_ENUM_SORT(xmv_context.reverse_enums[str(slsums[0])][0])
        case _:
            raise ValueError(f"Unsupported type: {xmv_type}")
        

def case_to_ite(case_expr: XMVCaseExpr, context: XMVContext, expr_map: dict[XMVExpr, MCILExpr]) -> MCILExpr:
    """Recursively translate a case expression to a series of cascaded ite expressions."""

    def _case_to_ite(branches: list[tuple[XMVExpr, XMVExpr]], i: int) -> MCILExpr:
        (cond, branch) = branches[i]

        if i >= len(branches)-1:
            return MCILApply(
                translate_type(branch.type, context),
                MCILIdentifier("ite", []),
                [
                    expr_map[cond],
                    expr_map[branch],
                    expr_map[branch]
                ]
            ) 

        return MCILApply(
            translate_type(branch.type, context),
            MCILIdentifier("ite", []),
            [
                expr_map[cond],
                expr_map[branch],
                _case_to_ite(branches, i+1)
            ]
        )

    return _case_to_ite(case_expr.branches, 0)

DEFINE_LET_VAR = lambda e: MCILVar(MCIL_NO_SORT, e, False)

def build_define_expr(
    expr: XMVIdentifier,
    context: XMVContext, 
    module: XMVModule
) -> MCILExpr:

    def dependent_defines(ident: str, context: XMVContext) -> list[XMVIdentifier]:
        stack: list[tuple[bool, XMVExpr]] = []
        visited: set[XMVExpr] = set()
        deps: list[XMVIdentifier] = []

        stack.append((False, context.defs[module.name][ident]))

        while len(stack) > 0:
            (seen, cur) = stack.pop()

            if cur in visited:
                continue
            elif seen:
                if isinstance(cur, XMVIdentifier) and cur.ident in context.defs[module.name]:
                    deps.append(cur)
                visited.add(cur)
                continue

            stack.append((True, cur))

            match cur:
                case XMVIdentifier(ident=ident):
                    if ident in context.defs[module.name]:
                        stack.append((False, context.defs[module.name][ident]))
                case XMVFunCall(args=args):
                    [stack.append((False, arg)) for arg in args]
                case XMVUnOp(arg=arg):
                    stack.append((False, arg))
                case XMVBinOp(lhs=lhs, rhs=rhs):
                    stack.append((False, lhs))
                    stack.append((False, rhs))
                case XMVIndexSubscript(array=array, index=index):
                    stack.append((False, array))
                    stack.append((False, index))
                case XMVWordBitSelection(word=word, low=_, high=_):
                    stack.append((False, word))
                case XMVSetBodyExpression(members=members):
                    [stack.append((False, m)) for m in members]
                case XMVTernary(cond=cond, then_expr=then_expr, else_expr=else_expr):
                    stack.append((False, cond))
                    stack.append((False, then_expr))
                    stack.append((False, else_expr))
                case XMVCaseExpr(branches=branches):
                    for (cond, then_expr) in branches:
                        stack.append((False, cond))
                        stack.append((False, then_expr))
                case _:
                    pass
        
        return deps

    emap = {}
    translate_expr(context.defs[module.name][expr.ident], context, emap, in_let_expr=True, module=module)
    ret = MCILLetExpr(
        MCIL_NO_SORT, 
        [(expr.ident, emap[context.defs[module.name][expr.ident]])], 
        DEFINE_LET_VAR(expr.ident)
    )

    for d in reversed(dependent_defines(expr.ident, context)):
        translate_expr(context.defs[module.name][d.ident], context, emap, in_let_expr=True, module=module)
        ret = MCILLetExpr(
            MCIL_NO_SORT, 
            [(d.ident, emap[context.defs[module.name][d.ident]])], 
            ret
        )

    return ret


def translate_expr(
    xmv_expr: XMVExpr, 
    context: XMVContext, 
    expr_map: dict[XMVExpr, MCILExpr],
    in_let_expr: bool,
    module: XMVModule
) -> None:
    """Updates `expr_map` to map all sub-expressions of `xmv_expr` to translated MCIL expressions."""
    for expr in postorder_nuxmv(xmv_expr, context):
        # logger.debug(f"TRANSLATING {expr} : {expr.type}", expr.__class__.__name__)

        if expr in expr_map:
            # print(f"{expr} in expr_map, {expr.type}, {expr_map[expr].sort}")
            continue

        match expr:
            case XMVIdentifier(ident=ident):
                # print(f"IDENTIFIER {ident}")

                if ident in context.defs[module.name] and not in_let_expr:
                    # print(f"{ident}: def case not let")
                    expr_map[expr] = build_define_expr(expr, context, module=module)
                elif ident in context.defs[module.name]:
                    # print(f"{ident}: def case")
                    expr_map[expr] = DEFINE_LET_VAR(expr.ident)
                elif ident in context.vars[module.name]:
                    # print(f"{ident}: var case")
                    expr_map[expr] = MCILVar(
                        sort=translate_type(context.vars[module.name][ident], context),
                        symbol=ident,
                        prime=False
                    )
                elif ident in context.reverse_enums:
                    # print(f"{ident}: enum case")
                    expr_map[expr] = MCILConstant(sort=MCIL_ENUM_SORT(context.reverse_enums[ident][0]), value=ident)
                elif expr.ident in context.module_params[module.name]:
                    # print(f"{ident}: param case")
                    ttype = translate_type(context.module_params[module.name][expr.ident], context)
                    # print(f"assigning {expr} : {ttype}")
                    expr_map[expr] = MCILVar(
                        sort=ttype,
                        symbol=ident,
                        prime=False
                    )
                else:
                    raise ValueError(f"Unrecognized var `{ident}`")
            case XMVIntegerConstant(integer=i):
                if i < 0:
                    expr_map[expr] = MCIL_INT_NEG_EXPR(MCILConstant(sort=MCIL_INT_SORT, value=-i))
                else:
                    expr_map[expr] =  MCILConstant(sort=MCIL_INT_SORT, value=i)
            case XMVBooleanConstant(boolean=b):
                expr_map[expr] =  MCILConstant(sort=MCIL_BOOL_SORT, value=b)
            case XMVWordConstant(width=width, value=value):
                expr_map[expr] =  MCILConstant(
                    sort=MCIL_BITVEC_SORT(width), 
                    value=int(value)
                )            
            case XMVFunCall(name=fname, args=fargs):
                match fname:
                    case "signed":
                        expr_map[expr] = expr_map[fargs[0]]
                    case "unsigned":
                        expr_map[expr] = expr_map[fargs[0]]
                    case "next":
                        # if not isinstance(fargs[0], XMVIdentifier):
                        #     raise ValueError("complex next expressions unsupported")
                        if isinstance(fargs[0], XMVModuleAccess):
                            # print(f'expr: {fargs[0]}')
                            # print(f"context: {context.vars}")
                            # print(f"accessing context.vars[{module.name}][{fargs[0].module}]")
                            # FIXME: I'm assuming that we know that mod_type will be a XMVModuleType
                            mod_type = cast(XMVModuleType, context.vars[module.name][fargs[0].module.ident])
                            # print(f"mod_type: {mod_type}")
                            mod_name = mod_type.module_name
                            module_access = fargs[0]
                            expr_map[expr] = MCILVar(
                                sort=translate_type(context.vars[mod_name][module_access.element.ident], context),
                                symbol=expr_map[fargs[0]].symbol, # FIXME: What is this line assuming about the type of expr_map[fargs[0]]? MCILExprs don't have a member `symbol` generally...
                                prime=True
                            )
                        elif isinstance(fargs[0], XMVIdentifier): # XMVIdentifier
                            ident = fargs[0].ident
                            if ident in context.vars[module.name]:
                                # print(f"ident found in variable map")
                                expr_map[expr] = MCILVar(
                                    sort=translate_type(context.vars[module.name][ident], context),
                                    symbol=ident,
                                    prime=True
                                )
                            elif ident in context.module_params[module.name]:
                                expr_map[expr] = MCILVar(
                                    sort=translate_type(context.module_params[module.name][ident], context),
                                    symbol=ident,
                                    prime=True
                                )
                            else:
                                raise ValueError(f"{ident} not in either variables or parameters = {context.module_params[module.name]}?")
                        else:
                            raise ValueError(f"Unsupported argument to next expression.")
                    case "READ":
                        expr_map[expr] = MCIL_SELECT_EXPR(
                            expr_map[fargs[0]],
                            expr_map[fargs[1]]
                        )
                    case "WRITE":
                        expr_map[expr] = MCIL_STORE_EXPR(
                            expr_map[fargs[0]],
                            expr_map[fargs[1]],
                            expr_map[fargs[2]]
                        )
                    case "typeof":
                        expr_map[expr] = expr_map[fargs[0]]
                    case "CONSTARRAY":
                        arr, val = fargs[0], fargs[1]
                        if isinstance(arr.type, XMVArray):
                            raise NotImplementedError()
                        elif isinstance(arr.type, XMVWordArray):
                            expr_map[expr] = MCIL_ARRAY_CONST(
                                MCIL_BITVEC_SORT(arr.type.word_length),
                                translate_type(arr.type.subtype, context),
                                expr_map[val]
                            )
                        else:
                            raise NotImplementedError()
                    case _:
                        expr_map[expr] = MCILApply(
                            sort=MCIL_NO_SORT,
                            identifier=MCILIdentifier(symbol=fname, indices=[]),
                            children=[expr_map[arg] for arg in fargs]
                        )
            case XMVBinOp(op=op, lhs=lhs, rhs=rhs):
                match op:
                    case '&':
                        il_op = "and" if isinstance(lhs.type, XMVBoolean) else "bvand"
                        il_lhs = expr_map[lhs]
                        il_rhs = expr_map[rhs]
                        # il_op = fn_map[("and", get_optype(lhs.type))]
                    case '|':
                        il_op = "or" if isinstance(lhs.type, XMVBoolean) else "bvor"
                        il_lhs = expr_map[lhs]
                        il_rhs = expr_map[rhs]
                        # il_op = fn_map[("or", get_optype(lhs.type))]
                    case 'xor':
                        il_op = "xor" if isinstance(lhs.type, XMVBoolean) else "bvxor"
                        il_lhs = expr_map[lhs]
                        il_rhs = expr_map[rhs]
                        # il_op = fn_map[("xor", get_optype(lhs.type))]
                    case "->":
                        il_op = "=>"
                        il_lhs = expr_map[lhs]
                        il_rhs = expr_map[rhs]
                    case "!=":
                        il_op = "distinct"
                        il_lhs = expr_map[lhs]
                        il_rhs = expr_map[rhs]
                    case "<":
                        if is_integer_type(lhs.type):
                            il_op = ">"
                        elif isinstance(lhs.type, XMVWord) and lhs.type.signed:
                            il_op = "bvslt"
                        else:
                            il_op = "bvult"
                        il_lhs = expr_map[lhs]
                        il_rhs = expr_map[rhs]
                        # il_op = "bvult"
                        # il_op = fn_map[("<", get_optype(lhs.type))]
                    case ">":
                        if is_integer_type(lhs.type):
                            il_op = ">"
                        elif isinstance(lhs.type, XMVWord) and lhs.type.signed:
                            il_op = "bvsgt"
                        else:
                            il_op = "bvugt"
                        il_lhs = expr_map[lhs]
                        il_rhs = expr_map[rhs]
                        # il_op = "bvugt"
                        # il_op = fn_map[(">", get_optype(lhs.type))]
                    case "<=":
                        if is_integer_type(lhs.type):
                            il_op = "<="
                        elif isinstance(lhs.type, XMVWord) and lhs.type.signed:
                            il_op = "bvsle"
                        else:
                            il_op = "bvule"
                        il_lhs = expr_map[lhs]
                        il_rhs = expr_map[rhs]
                        # il_op = "bvule"
                        # il_op = fn_map[("<=", get_optype(lhs.type))]
                    case ">=":
                        if is_integer_type(lhs.type):
                            il_op = ">="
                        elif isinstance(lhs.type, XMVWord) and lhs.type.signed:
                            il_op = "bvsge"
                        else:
                            il_op = "bvuge"
                        il_lhs = expr_map[lhs]
                        il_rhs = expr_map[rhs]
                        # il_op = "bvuge"
                        # il_op = fn_map[(">=", get_optype(lhs.type))]
                    case "+":
                        il_op = "+" if isinstance(lhs.type, XMVInteger) else "bvadd"
                        il_lhs = expr_map[lhs]
                        il_rhs = expr_map[rhs]
                        # il_op = "bvadd"
                        # il_op = fn_map[("+", get_optype(lhs.type))]
                    case "*":
                        il_op = "*" if isinstance(lhs.type, XMVInteger) else "bvmul"
                        il_lhs = expr_map[lhs]
                        il_rhs = expr_map[rhs]
                        # il_op = "bvmul"
                        # il_op = fn_map[("*", get_optype(lhs.type))]
                    case "/":
                        expr_type = cast(XMVWord, expr.type)
                        il_op = "bvsdiv" if expr_type.signed else "bvudiv"
                        il_lhs = expr_map[lhs]
                        il_rhs = expr_map[rhs]
                    case ">>":
                        il_op = "bvashr"
                        il_lhs = expr_map[lhs]
                        il_rhs = expr_map[rhs]
                    case "<<":
                        il_op = "bvshl"
                        il_lhs = expr_map[lhs]
                        il_rhs = expr_map[rhs]
                    case 'mod':
                        il_op = "bvsmod"
                        il_lhs = expr_map[lhs]
                        il_rhs = expr_map[rhs]
                    case "=" | "<->":
                        il_op = "="
                        try:
                            il_lhs_sort = translate_type(lhs.type, context)
                            if is_int_sort(il_lhs_sort):
                                il_lhs = expr_map[lhs]
                                il_rhs = expr_map[rhs]
                            else:
                                il_lhs = expr_map[lhs]
                                il_rhs = expr_map[rhs]
                        except ValueError:
                            try:
                                il_rhs_sort = translate_type(rhs.type, context)
                                if is_int_sort(il_rhs_sort):
                                    il_rhs = expr_map[rhs]
                                    il_lhs = expr_map[lhs]
                                else:
                                    il_lhs = expr_map[lhs]
                                    il_rhs = expr_map[rhs]
                            except ValueError:
                                il_lhs = expr_map[lhs]
                                il_rhs = expr_map[rhs]
                    case _:
                        il_op = op
                        il_lhs = expr_map[lhs]
                        il_rhs = expr_map[rhs]


                expr_map[expr] =  MCILApply(
                    sort=translate_type(expr.type, context),
                    identifier=MCILIdentifier(symbol=il_op, indices=[]),
                    children=[il_lhs, il_rhs]
                )
            case XMVUnOp(op=op, arg=arg):
                match op:
                    case "!":
                        il_op = "not" if isinstance(arg.type, XMVBoolean) else "bvnot"
                    case "-":
                        il_op = "-" if isinstance(arg.type, XMVInteger) else "bvneg"
                    case _:
                        il_op = op

                expr_map[expr] =  MCILApply(
                    sort=translate_type(expr.type, context),
                    identifier=MCILIdentifier(symbol=il_op, indices=[]),
                    children=[expr_map[arg]]
                )
            case XMVWordBitSelection(word=word, low=low, high=high):
                expr_map[expr] =  MCILApply(
                    sort=translate_type(expr.type, context),
                    identifier=MCILIdentifier(symbol="extract", indices=[high, low]),
                    children=[expr_map[word]]
                )
            case XMVCaseExpr():
                expr_map[expr] =  case_to_ite(expr, context, expr_map)
            case XMVModuleAccess(module=ma_module, element=ma_elem):
                expr_map[expr] = MCILVar(
                    sort=translate_type(expr.type, context),
                    symbol=ma_module.ident + "." + ma_elem.ident,
                    prime=False
                )
            case _:
                raise ValueError(f"unhandled expression {expr}, {expr.__class__}")


def conjoin_list(expr_list: list[MCILExpr]) -> MCILExpr:
    if len(expr_list) == 0:
        return MCIL_BOOL_CONST(True)
    elif len(expr_list) == 1:
        return expr_list[0]
    else:
        return MCIL_AND_EXPR(expr_list)


def gather_input(xmv_module: XMVModule, context: XMVContext) -> list[tuple[str, MCILSort]]:
    result: list[tuple[str, MCILSort]] = []

    for param in xmv_module.parameters:
        # v = MCILVar(
        #     sort=,
        #     symbol=param.ident, # type: ignore
        #     prime=False
        # )
        result.append((param, translate_type(context.module_params[xmv_module.name][param], context)))

    for module_element in xmv_module.elements:
        match module_element:
            case XMVVarDeclaration(modifier="IVAR"):
                for (var_name, xmv_var_type) in module_element.var_list:
                    if isinstance(xmv_var_type, XMVModuleType):
                        continue

                    result.append((var_name.ident, translate_type(xmv_var_type, context)))
            case _:
                pass
    
    return result


def gather_local(xmv_module: XMVModule, context: XMVContext) -> list[tuple[str, MCILSort]]:
    result: list[tuple[str, MCILSort]] = []
    for e in [e for e in xmv_module.elements if isinstance(e, XMVVarDeclaration)]:
        for (var_name, xmv_var_type) in e.var_list: 
            if isinstance(xmv_var_type, XMVModuleType):
                context.module_locals[var_name.ident] = []
                # gathering submodule inputs
                for name in context.module_params[xmv_var_type.module_name]:
                    type = context.module_params[xmv_var_type.module_name][name]
                    input_var = MCILVar(
                            sort=translate_type(type, context),
                            symbol=var_name.ident + "." + name,
                            prime=False
                        )
                    result.append((var_name.ident + "." + name, translate_type(type, context)))
                    context.module_locals[var_name.ident].append(input_var)

                # gathering submodule outputs
                    
                for (var_symbol, var_sort) in context.outputs[xmv_var_type.module_name]:
                    local_var = MCILVar(
                        sort=var_sort,
                        symbol=var_name.ident + "." + var_symbol,
                        prime=False
                    )
                    result.append((var_name.ident + "." + var_symbol, var_sort))
                    context.module_locals[var_name.ident].append(local_var)

    return result


def gather_output(xmv_module: XMVModule, context: XMVContext) -> list[tuple[str, MCILSort]]:
    result: list[tuple[str, MCILSort]] = []
    
    for module_element in xmv_module.elements:
        match module_element:
            case XMVVarDeclaration(modifier="VAR") | XMVVarDeclaration(modifier="FROZENVAR"):
                for (var_name, xmv_var_type) in module_element.var_list:
                    match xmv_var_type:
                        case XMVEnumeration(summands=summands):
                            if xmv_var_type.is_integer():
                                # values = {int(s) for s in expr.type.summands}
                                # expr.type = XMVInteger(values)
                                il_type = MCIL_INT_SORT
                            else:
                                lsummands = list(summands)
                                slsummands = [str(s) for s in lsummands]

                                il_symbol = context.reverse_enums[slsummands[0]][0]
                                il_type = MCIL_ENUM_SORT(il_symbol)
                        case XMVModuleType(module_name=module_name):
                            gather_output(context.modules[module_name], context)
                            continue
                        case _:
                            il_type = translate_type(xmv_var_type, context)

                    result.append((var_name.ident, il_type))
            case XMVDefineDeclaration(define_list=define_list):
                for define in [
                    define
                    for define 
                    in define_list 
                    if define.name.ident in context.referenced_defs[xmv_module.name]
                ]:
                    il_type = translate_type(context.defs[xmv_module.name][define.name.ident].type, context)
                    result.append((define.name.ident, il_type))
            case _:
               pass
    
    context.outputs[xmv_module.name] = result

    return result


def specialize_variable(module_name: str, var: MCILVar) -> MCILVar:
    return MCILVar(
        sort=var.sort,
        symbol=module_name + "." + var.symbol,
        prime=var.prime
    )


def specialize_vars_in_expr(module_name: str, expr: MCILExpr) -> MCILExpr:
    match expr:
        case MCILVar():
            return specialize_variable(module_name, expr)
        case MCILApply(sort=sort, identifier=identifier, children=children):
            schildren = []
            for child in children:
                schildren.append(specialize_vars_in_expr(module_name, child))
            return MCILApply(sort=sort, identifier=identifier, children=schildren)
        case _:
            return MCIL_BOOL_CONST(True)
            # print("CATCH ALL CASE:", expr, expr.__class__.__name__)


def gather_init(xmv_module: XMVModule, context: XMVContext, expr_map: dict[XMVExpr, MCILExpr]) -> MCILExpr:
    init_list: list[MCILExpr] = []
    
    for init_decl in [e for e in xmv_module.elements if isinstance(e, XMVInitDeclaration)]:
        translate_expr(init_decl.formula, context, expr_map, in_let_expr=False, module=xmv_module)
        init_list.append(expr_map[init_decl.formula])
    
    for module_element in xmv_module.elements:
        match module_element:
            case XMVAssignDeclaration(assign_list=al):
                for assign_decl in al:
                    if assign_decl.modifier == "init":
                        translate_expr(assign_decl.lhs, context, expr_map, in_let_expr=False, module=xmv_module)
                        translate_expr(assign_decl.rhs, context, expr_map, in_let_expr=False, module=xmv_module)

                        init_expr = MCIL_EQ_EXPR([expr_map[assign_decl.lhs], 
                                                 expr_map[assign_decl.rhs]])
                        
                        init_list.append(init_expr)
            case _:
                pass

    return conjoin_list(init_list)


def gather_trans(xmv_module: XMVModule, context: XMVContext, expr_map: dict[XMVExpr, MCILExpr]) -> MCILExpr:
    trans_list: list[MCILExpr] = []
    
    for trans_decl in [e for e in xmv_module.elements if isinstance(e, XMVTransDeclaration)]:
        translate_expr(trans_decl.formula, context, expr_map, in_let_expr=False, module=xmv_module)
        trans_list.append(expr_map[trans_decl.formula])

    for module_element in xmv_module.elements:
        match module_element:
            case XMVAssignDeclaration(assign_list=al):
                for assign_decl in al:
                    if assign_decl.modifier == "next":
                        translate_expr(assign_decl.rhs, context, expr_map, in_let_expr=False, module=xmv_module)

                        if isinstance(assign_decl.lhs, XMVIdentifier):
                            lhs_expr = MCILVar(
                                        sort=translate_type(assign_decl.rhs.type, context),
                                        symbol=assign_decl.lhs.ident,
                                        prime=True
                                    )
                        else:
                            raise ValueError(f"Unsupported: next(complex_identifier)")

                        trans_expr = MCIL_EQ_EXPR([lhs_expr, 
                                                  expr_map[assign_decl.rhs]])
                        
                        trans_list.append(trans_expr)
            case _:
                pass

    return conjoin_list(trans_list) if len(trans_list) > 0 else MCIL_BOOL_CONST(True)


def gather_inv(xmv_module: XMVModule, context: XMVContext, expr_map: dict[XMVExpr, MCILExpr]) -> MCILExpr:
    inv_list: list[MCILExpr] = []
    
    # things marked explicitly as INVAR
    # print("inv - looking for INVAR")
    for inv_decl in [e for e in xmv_module.elements if isinstance(e, XMVInvarDeclaration)]:
        translate_expr(inv_decl.formula, context, expr_map, in_let_expr=False, module=xmv_module)
        inv_list.append(expr_map[inv_decl.formula])

    # standard ASSIGN declarations (without init/next modifiers)
    # print("inv - looking through ASSIGN")
    for module_element in xmv_module.elements:
        match module_element:
            case XMVAssignDeclaration(assign_list=al):
                for assign_decl in al:
                    if assign_decl.modifier == "none":
                        
                        translate_expr(assign_decl.rhs, context, expr_map, in_let_expr=False, module=xmv_module)

                        if isinstance(assign_decl.lhs, XMVIdentifier):
                            lhs_expr = MCILVar(
                                        sort=translate_type(assign_decl.rhs.type, context),
                                        symbol=assign_decl.lhs.ident,
                                        prime=False
                                    )
                        else:
                            raise ValueError(f"Unsupported: next(complex_identifier)")

                        inv_expr = MCIL_EQ_EXPR([lhs_expr, expr_map[assign_decl.rhs]])
                        
                        inv_list.append(inv_expr)
            case XMVVarDeclaration(modifier="FROZENVAR", var_list=var_list):
                for (var_name, _) in var_list:
                    var_ident = var_name.ident
                    inv_list.append(MCIL_EQ_EXPR([
                        MCILVar(
                            sort=translate_type(context.vars[xmv_module.name][var_ident], context),
                            symbol=var_ident,
                            prime=False
                        ),
                        MCILVar(
                            sort=translate_type(context.vars[xmv_module.name][var_ident], context),
                            symbol=var_ident,
                            prime=True
                        )
                    ]))
            case XMVVarDeclaration(var_list=var_list):
                # All integer enums must be constrained where they are declared
                # Example: 
                #   var: {0,1,2}
                # should have MCIL constraint
                #   :inv (and ... (or (= var 0) (= var 1) (= var 2)) ...)
                for (var_name, var_type) in [
                    (var_name, var_type)
                    for (var_name, var_type)
                    in var_list
                    if isinstance(var_type, XMVEnumeration) and var_type.is_integer()
                ]:
                    var_ident = var_name.ident
                    inv_list.append(MCIL_OR_EXPR([
                        MCIL_EQ_EXPR([
                            MCILVar(MCIL_INT_SORT, var_ident, False),
                            MCIL_INT_CONST(int(value))
                        ])
                        for value
                        in var_type.summands
                    ]))
                    
            case XMVDefineDeclaration(define_list=define_list):
                for define in [
                    define
                    for define 
                    in define_list 
                    if define.name.ident in context.referenced_defs[xmv_module.name]
                ]:
                    translate_expr(
                        context.defs[xmv_module.name][define.name.ident], context, expr_map, False, xmv_module
                    )
                    il_type = translate_type(context.defs[xmv_module.name][define.name.ident].type, context)
                    inv_list.append(MCIL_EQ_EXPR([
                        MCILVar(
                            sort=il_type,
                            symbol=define.name.ident,
                            prime=False
                        ),
                        expr_map[context.defs[xmv_module.name][define.name.ident]]
                    ]))
            case _:
                pass

    # module variable instantiations
    # print("inv - looking through module instantiations")
    for var_list in [vd.var_list for vd in xmv_module.elements if isinstance(vd, XMVVarDeclaration)]:
        for (var_name, var_type) in var_list:
            match var_type:
                case XMVModuleType(module_name=module_name, parameters=parameters):
                    for i, param in enumerate(parameters):
                        # print(f"found parameter {param}")
                        match param:
                            case XMVModuleAccess(module=module, element=elem):
                                if isinstance(module, XMVModuleAccess):
                                    module_to_check = module.element
                                else:
                                    module_to_check = module.ident

                                mod_typ = context.vars[xmv_module.name][module.ident]
                                source_module = mod_typ.module_name

                                if elem in context.defs[source_module]: # if the module access refers to a def'd element, specialize it and construct expr
                                    translate_expr(context.defs[source_module][elem], context, expr_map, in_let_expr=False, module=context.modules[module_name])
                                    defn = expr_map[context.defs[source_module][elem]]
                                    sdefn = specialize_vars_in_expr(var_name.ident, defn)
                                    init_expr = MCIL_EQ_EXPR([context.module_locals[var_name.ident][i], sdefn])
                                    inv_list.append(init_expr)
                                else:
                                    translate_expr(param, context, expr_map, in_let_expr=False, module=xmv_module)
                                    init_expr = MCIL_EQ_EXPR([context.module_locals[var_name.ident][i], expr_map[param]])
                                    inv_list.append(init_expr)
                            case _:
                                translate_expr(param, context, expr_map, in_let_expr=False, module=xmv_module)
                                init_expr = MCIL_EQ_EXPR([context.module_locals[var_name.ident][i], expr_map[param]])
                                inv_list.append(init_expr)


                case _:
                    pass

    # print("inv - done")
    return conjoin_list(inv_list) if len(inv_list) > 0 else MCIL_BOOL_CONST(True)

def gather_subsystems(xmv_module: XMVModule, xmv_context: XMVContext) -> dict[str, tuple[str, list[str]]]:
    subsystems: dict[str, tuple[str, list[str]]] = {}

    for e in [e for e in xmv_module.elements if isinstance(e, XMVVarDeclaration)]:
        for (var_name, xmv_var_type) in e.var_list: 
            if isinstance(xmv_var_type, XMVModuleType):
                subsystems[var_name.ident] = (xmv_var_type.module_name,
                                              list(map(lambda x : x.symbol, xmv_context.module_locals[var_name.ident])))

    return subsystems


def gather_consts(xmv_module: XMVModule) -> list[MCILCommand]:
    return []


def gather_invarspecs(xmv_module: XMVModule, context: XMVContext, expr_map: dict[XMVExpr, MCILExpr]) -> dict[str, MCILExpr]:
    invarspec_dict: dict[str, MCILExpr] = {}

    spec_num = 1
    for invarspec_decl in [e for e in xmv_module.elements if isinstance(e, XMVInvarspecDeclaration)]:
        xmv_expr = invarspec_decl.formula
        translate_expr(xmv_expr, context, expr_map, in_let_expr=False, module=xmv_module)

        invarspec_dict[f"rch_{spec_num}"] = (
            cast(MCILExpr, MCILApply(
                MCIL_BOOL_SORT, 
                MCILIdentifier("not", []), 
                [expr_map[xmv_expr]]
            )))
            
        spec_num += 1

    return invarspec_dict


def translate_module(xmv_module: XMVModule, context: XMVContext) -> list[MCILCommand]:
    module_name = xmv_module.name

    logger.debug(f"Translating module {module_name}")

    logger.debug(f"Translating enums")
    # enums = gather_enums(xmv_module, context)

    logger.debug(f"Translating input variables")
    input = gather_input(xmv_module, context)

    logger.debug(f"Translating output variables")
    output = gather_output(xmv_module, context)

    logger.debug(f"Translating local variables")
    local = gather_local(xmv_module, context)

    logger.debug(f"Translating initialization constraints")
    emap = {}
    init = gather_init(xmv_module, context, emap)

    logger.debug(f"Translating transition relation")
    trans = gather_trans(xmv_module, context, emap)

    logger.debug(f"Translating invariant constraints")
    inv = gather_inv(xmv_module, context, emap)

    subsystems = gather_subsystems(xmv_module, context)

    define_system: MCILCommand = MCILDefineSystem(
            symbol=xmv_module.name,
            input=input,
            output=output,
            local=local,
            init=init,
            trans=trans,
            inv=inv,
            subsystems=subsystems
        )
    
    reachable: dict[str, MCILExpr] = gather_invarspecs(xmv_module, context, emap)

    if len(reachable) == 0:
        check_system: list[MCILCommand] = []
    else:
        check_system: list[MCILCommand] = [MCILCheckSystem(
                symbol=xmv_module.name,
                input=input,
                output=output,
                local=local,
                assumption={},
                fairness={},
                reachable=reachable,
                current={},
                query={f"qry_{r}":[r] for r in reachable.keys()},
                queries=[]
            )]

    # commands
    # consts: list[MCILCommand] = gather_consts(xmv_module)

    return [define_system] + check_system


def infer_logic(commands: list[MCILCommand]) -> Optional[MCILSetLogic]:
    for def_sys in [s for s in commands if isinstance(s, MCILDefineSystem)]:
        variables = def_sys.input + def_sys.output + def_sys.local
        for _,sort in variables:
            if is_int_sort(sort):
                return MCILSetLogic(logic="QF_LIA")
            
            if is_bitvec_sort(sort):
                return MCILSetLogic(logic="QF_ABV")
        
    return


def translate(xmv_program: XMVProgram) -> Optional[MCILProgram]:

    logger.info(f"Type checking")
    context = XMVContext(xmv_program.modules)
    well_typed = type_check_module(xmv_program.main, context)

    if not well_typed:
        logger.error(f"Failed type checking")
        return None

    commands: list[MCILCommand] = []
    commands += [
        MCILDeclareEnumSort(symbol, [str(s) for s in enum.summands])
        for symbol,enum
        in context.enums.items()
        if enum.is_symbolic()
    ]
    
    for module in reversed(context.module_dep_order):
        commands += translate_module(xmv_module=module, context=context)

    logic: Optional[MCILSetLogic] = infer_logic(commands)
    if logic:
        logger.debug(f"inferred SMT logic {logic.logic}")
        commands = [logic] + commands

    return MCILProgram(commands=commands)


def translate_file(
    input_path: Path, 
    output_path: Path, 
    do_cpp: bool
) -> int:
    """Parses, type checks, translates, and writes the translation result of `input_path` to `output_path`. Runs C preprocessor if `do_cpp` is True. Returns 0 on success, 1 otherwise."""
    logger.info(f"Parsing specification in {input_path}")
    parse_tree = parse(input_path, do_cpp)
    if not parse_tree:
        logger.error(f"Failed parsing specification in {input_path}")
        return 1

    logger.info(f"Translating specification in {input_path}")
    result = translate(parse_tree)
    if not result:
        logger.error(f"Failed translating specification in {input_path}")
        return 1

    logger.info(f"Writing output to {output_path}")

    with open(str(output_path), "w") as f:
        f.write(str(result))
        logger.info(f"Wrote output to {output_path}")

    return 0