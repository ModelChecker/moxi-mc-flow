import pathlib
from typing import cast, Optional

from src import log
from src import parse_nuxmv
from src import nuxmv
from src import mcil

FILE_NAME = pathlib.Path(__file__).name

# TODO: Simplify expression handling with function map
# fn_map: dict[tuple[str, OpType], str] = {
#     ("&", OpType.BOOL_SORT): "and", ("&", OpType.BITVEC_SORT): "bvand",
#     ("|", OpType.BOOL_SORT): "or", ("|", OpType.BITVEC_SORT): "bvor",
#     ("xor", OpType.BOOL_SORT): "xor", ("xor", OpType.BITVEC_SORT): "bvxor",
#     # ("xnor", mcil.MCIL_BOOL_SORT): "xnor", ("xnor", mcil.MCIL_BITVEC_SORT): "bvxor",
#     ("->", OpType.BOOL_SORT): "=>",
#     ("!=", OpType.BOOL_SORT): "distinct",
#     (">=", OpType.INT_SORT): ">=", (">=", OpType.BITVEC_SORT): "bvuge",
#     ("<=", OpType.INT_SORT): "<=", ("<=", OpType.BITVEC_SORT): "bvule",
#     ("<", OpType.INT_SORT): "<", ("<", OpType.BITVEC_SORT): "bvult",
#     (">", OpType.INT_SORT): ">", (">", OpType.BITVEC_SORT): "bvugt",
#     ("+", OpType.INT_SORT): "+", ("+", OpType.BITVEC_SORT): "bvadd",
#     ("*", OpType.INT_SORT): "*", ("*", OpType.BITVEC_SORT): "bvmul",
# }

def translate_type(xmv_type: nuxmv.XMVType, xmv_context: nuxmv.XMVContext) -> mcil.MCILSort:
    match xmv_type:
        case nuxmv.XMVBoolean():
            return mcil.MCIL_BOOL_SORT
        case nuxmv.XMVInteger():
            return mcil.MCIL_INT_SORT
        case nuxmv.XMVReal():
            raise ValueError("nuXmv `real` type not supported in the IL (yet?)")
        case nuxmv.XMVClock():
            raise ValueError("nuXmv `clock` type not supported in the IL (yet?)")
        case nuxmv.XMVWord(width=w):
            return mcil.MCIL_BITVEC_SORT(int(w))
        case nuxmv.XMVArray(subtype=t):
            return mcil.MCIL_ARRAY_SORT(mcil.MCIL_INT_SORT, translate_type(t, xmv_context))
        case nuxmv.XMVWordArray(word_length=wl, subtype=t):
            return mcil.MCIL_ARRAY_SORT(mcil.MCIL_BITVEC_SORT(int(wl)), translate_type(t, xmv_context))
        case nuxmv.XMVModuleType():
            raise ValueError(f"Cannot translate type {xmv_type}")
        case nuxmv.XMVEnumeration():
            if xmv_type.is_integer():
                return mcil.MCIL_INT_SORT
            
            """
            As for enums, we'll have to handle those a bit differently than we are right now (at least symbolic ones). Because right now, in SMV, you may have two variables like:

            v1: {s0, s1};
            v2: {s0, s1, s2};

            And something like: (v1 = v2) is a totally valid expression. But in the translation, they are both translated to different enum types entirely, which won't be well-sorted. Instead, we need all symbolic enum type to be translated to the same mcil.MCIL enum sort, then constrain them like:

            (declare-enum-sort enums (s0 s1 s2))
            (define-system ...
            :local ((v1 enums) (v2 enums))
            :inv (and (or (= v1 s0) (= v1 s1)) (or (= v2 s0) (= v2 s1) (=v2 s2))

            I'm not sure any of the benchmarks exhibit this, but it's something to keep in mind.
            """

            sums = xmv_type.summands
            lsums = list(sums)
            slsums = [str(s) for s in lsums]

            return mcil.MCIL_ENUM_SORT(xmv_context.reverse_enums[str(slsums[0])][0])
        case _:
            raise ValueError(f"Unsupported type: {xmv_type}")
        

def case_to_ite(case_expr: nuxmv.XMVCaseExpr, context: nuxmv.XMVContext, expr_map: dict[nuxmv.XMVExpr, mcil.MCILExpr]) -> mcil.MCILExpr:
    """Recursively translate a case expression to a series of cascaded ite expressions."""

    def _case_to_ite(branches: list[tuple[nuxmv.XMVExpr, nuxmv.XMVExpr]], i: int) -> mcil.MCILExpr:
        (cond, branch) = branches[i]

        if i >= len(branches)-1:
            return mcil.MCILApply(
                translate_type(branch.type, context),
                mcil.MCILIdentifier("ite", []),
                [
                    expr_map[cond],
                    expr_map[branch],
                    expr_map[branch]
                ]
            ) 

        return mcil.MCILApply(
            translate_type(branch.type, context),
            mcil.MCILIdentifier("ite", []),
            [
                expr_map[cond],
                expr_map[branch],
                _case_to_ite(branches, i+1)
            ]
        )

    return _case_to_ite(case_expr.branches, 0)

DEFINE_LET_VAR = lambda e: mcil.MCILVar(mcil.MCIL_NO_SORT, e, False)

def build_define_expr(
    expr: nuxmv.XMVIdentifier,
    context: nuxmv.XMVContext, 
    module: nuxmv.XMVModuleDeclaration
) -> mcil.MCILExpr:
    
    log.debug(f"building define expr {expr}", FILE_NAME)

    def dependent_defines(ident: str, context: nuxmv.XMVContext) -> list[nuxmv.XMVIdentifier]:
        stack: list[tuple[bool, nuxmv.XMVExpr]] = []
        visited: set[nuxmv.XMVExpr] = set()
        deps: list[nuxmv.XMVIdentifier] = []

        stack.append((False, context.defs[module.name][ident]))

        while len(stack) > 0:
            (seen, cur) = stack.pop()

            if cur in visited:
                continue
            elif seen:
                if isinstance(cur, nuxmv.XMVIdentifier) and cur.ident in context.defs[module.name]:
                    deps.append(cur)
                visited.add(cur)
                continue

            stack.append((True, cur))

            match cur:
                case nuxmv.XMVIdentifier(ident=ident):
                    if ident in context.defs[module.name]:
                        stack.append((False, context.defs[module.name][ident]))
                case nuxmv.XMVFunCall(args=args):
                    [stack.append((False, arg)) for arg in args]
                case nuxmv.XMVUnOp(arg=arg):
                    stack.append((False, arg))
                case nuxmv.XMVBinOp(lhs=lhs, rhs=rhs):
                    stack.append((False, lhs))
                    stack.append((False, rhs))
                case nuxmv.XMVIndexSubscript(array=array, index=index):
                    stack.append((False, array))
                    stack.append((False, index))
                case nuxmv.XMVWordBitSelection(word=word, low=_, high=_):
                    stack.append((False, word))
                case nuxmv.XMVSetBodyExpression(members=members):
                    [stack.append((False, m)) for m in members]
                case nuxmv.XMVTernary(cond=cond, then_expr=then_expr, else_expr=else_expr):
                    stack.append((False, cond))
                    stack.append((False, then_expr))
                    stack.append((False, else_expr))
                case nuxmv.XMVCaseExpr(branches=branches):
                    for (cond, then_expr) in branches:
                        stack.append((False, cond))
                        stack.append((False, then_expr))
                case _:
                    pass
        
        return deps

    emap = {}
    translate_expr(context.defs[module.name][expr.ident], context, emap, in_let_expr=True, module=module)
    ret = mcil.MCILLetExpr(
        mcil.MCIL_NO_SORT, 
        [(expr.ident, emap[context.defs[module.name][expr.ident]])], 
        DEFINE_LET_VAR(expr.ident)
    )

    for d in reversed(dependent_defines(expr.ident, context)):
        log.debug(str(d), FILE_NAME)
        translate_expr(context.defs[module.name][d.ident], context, emap, in_let_expr=True, module=module)
        ret = mcil.MCILLetExpr(
            mcil.MCIL_NO_SORT, 
            [(d.ident, emap[context.defs[module.name][d.ident]])], 
            ret
        )

    return ret


def translate_expr(
    xmv_expr: nuxmv.XMVExpr, 
    context: nuxmv.XMVContext, 
    expr_map: dict[nuxmv.XMVExpr, mcil.MCILExpr],
    in_let_expr: bool,
    module: nuxmv.XMVModuleDeclaration
) -> None:
    """Updates `expr_map` to map all sub-expressions of `xmv_expr` to translated mcil.MCIL expressions."""
    for expr in nuxmv.postorder_nuxmv(xmv_expr, context, False):
        if expr in expr_map:
            continue

        match expr:
            case nuxmv.XMVIdentifier(ident=ident):
                # print(f"IDENTIFIER {ident}")

                if ident in context.defs[module.name] and not in_let_expr:
                    # print(f"{ident}: def case not let")
                    expr_map[expr] = build_define_expr(expr, context, module=module)
                elif ident in context.defs[module.name]:
                    # print(f"{ident}: def case")
                    expr_map[expr] = DEFINE_LET_VAR(expr.ident)
                elif (ident in context.vars[module.name] 
                      and isinstance(context.vars[module.name][ident], nuxmv.XMVModuleType)
                ):
                    # Skip over any module variables that come up in traversal
                    # These are all module accesses -- relevant for type checking but not here 
                    pass
                elif ident in context.vars[module.name]:
                    # print(f"{ident}: var case")
                    expr_map[expr] = mcil.MCILVar(
                        sort=translate_type(context.vars[module.name][ident], context),
                        symbol=ident,
                        prime=False
                    )
                elif ident in context.reverse_enums:
                    # print(f"{ident}: enum case")
                    expr_map[expr] = mcil.MCILConstant(sort=mcil.MCIL_ENUM_SORT(context.reverse_enums[ident][0]), value=ident)
                elif expr.ident in context.module_params[module.name]:
                    # print(f"{ident}: param case")
                    ttype = translate_type(context.module_params[module.name][expr.ident], context)
                    # print(f"assigning {expr} : {ttype}")
                    expr_map[expr] = mcil.MCILVar(
                        sort=ttype,
                        symbol=ident,
                        prime=False
                    )
                else:
                    raise ValueError(f"Unrecognized var `{ident}`")
            case nuxmv.XMVIntegerConstant(integer=i):
                if i < 0:
                    expr_map[expr] = mcil.MCIL_INT_NEG_EXPR(mcil.MCILConstant(sort=mcil.MCIL_INT_SORT, value=-i))
                else:
                    expr_map[expr] =  mcil.MCILConstant(sort=mcil.MCIL_INT_SORT, value=i)
            case nuxmv.XMVBooleanConstant(boolean=b):
                expr_map[expr] =  mcil.MCILConstant(sort=mcil.MCIL_BOOL_SORT, value=b)
            case nuxmv.XMVWordConstant(width=width, value=value):
                expr_map[expr] =  mcil.MCILConstant(
                    sort=mcil.MCIL_BITVEC_SORT(width), 
                    value=int(value)
                )            
            case nuxmv.XMVFunCall(name=fname, args=fargs):
                match fname:
                    case "signed":
                        expr_map[expr] = expr_map[fargs[0]]
                    case "unsigned":
                        expr_map[expr] = expr_map[fargs[0]]
                    case "next":
                        # if not isinstance(fargs[0], nuxmv.XMVIdentifier):
                        #     raise ValueError("complex next expressions unsupported")
                        if isinstance(fargs[0], nuxmv.XMVModuleAccess):
                            # print(f'expr: {fargs[0]}')
                            # print(f"context: {context.vars}")
                            # print(f"accessing context.vars[{module.name}][{fargs[0].module}]")
                            # FIXME: I'm assuming that we know that mod_type will be a nuxmv.XMVModuleType
                            mod_type = cast(nuxmv.XMVModuleType, context.vars[module.name][fargs[0].module.ident])
                            # print(f"mod_type: {mod_type}")
                            mod_name = mod_type.module_name
                            module_access = fargs[0]
                            expr_map[expr] = mcil.MCILVar(
                                sort=translate_type(context.vars[mod_name][module_access.element.ident], context),
                                symbol=expr_map[fargs[0]].symbol, # FIXME: What is this line assuming about the type of expr_map[fargs[0]]? mcil.MCILExprs don't have a member `symbol` generally...
                                prime=True
                            )
                        elif isinstance(fargs[0], nuxmv.XMVIdentifier): # nuxmv.XMVIdentifier
                            ident = fargs[0].ident
                            if ident in context.vars[module.name]:
                                # print(f"ident found in variable map")
                                expr_map[expr] = mcil.MCILVar(
                                    sort=translate_type(context.vars[module.name][ident], context),
                                    symbol=ident,
                                    prime=True
                                )
                            elif ident in context.module_params[module.name]:
                                expr_map[expr] = mcil.MCILVar(
                                    sort=translate_type(context.module_params[module.name][ident], context),
                                    symbol=ident,
                                    prime=True
                                )
                            else:
                                raise ValueError(f"{ident} not in either variables or parameters = {context.module_params[module.name]}?")
                        else:
                            raise ValueError(f"Unsupported argument to next expression.")
                    case "READ":
                        expr_map[expr] = mcil.MCIL_SELECT_EXPR(
                            expr_map[fargs[0]],
                            expr_map[fargs[1]]
                        )
                    case "WRITE":
                        expr_map[expr] = mcil.MCIL_STORE_EXPR(
                            expr_map[fargs[0]],
                            expr_map[fargs[1]],
                            expr_map[fargs[2]]
                        )
                    case "typeof":
                        expr_map[expr] = expr_map[fargs[0]]
                    case "CONSTARRAY":
                        arr, val = fargs[0], fargs[1]
                        if isinstance(arr.type, nuxmv.XMVArray):
                            raise NotImplementedError()
                        elif isinstance(arr.type, nuxmv.XMVWordArray):
                            expr_map[expr] = mcil.MCIL_ARRAY_CONST(
                                mcil.MCIL_BITVEC_SORT(arr.type.word_length),
                                translate_type(arr.type.subtype, context),
                                expr_map[val]
                            )
                        else:
                            raise NotImplementedError()
                    case _:
                        expr_map[expr] = mcil.MCILApply(
                            sort=mcil.MCIL_NO_SORT,
                            identifier=mcil.MCILIdentifier(symbol=fname, indices=[]),
                            children=[expr_map[arg] for arg in fargs]
                        )
            case nuxmv.XMVBinOp(op=op, lhs=lhs, rhs=rhs):
                match op:
                    case '&':
                        il_op = "and" if isinstance(lhs.type, nuxmv.XMVBoolean) else "bvand"
                        il_lhs = expr_map[lhs]
                        il_rhs = expr_map[rhs]
                        # il_op = fn_map[("and", get_optype(lhs.type))]
                    case '|':
                        il_op = "or" if isinstance(lhs.type, nuxmv.XMVBoolean) else "bvor"
                        il_lhs = expr_map[lhs]
                        il_rhs = expr_map[rhs]
                        # il_op = fn_map[("or", get_optype(lhs.type))]
                    case 'xor':
                        il_op = "xor" if isinstance(lhs.type, nuxmv.XMVBoolean) else "bvxor"
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
                        if nuxmv.is_integer_type(lhs.type):
                            il_op = ">"
                        elif isinstance(lhs.type, nuxmv.XMVWord) and lhs.type.signed:
                            il_op = "bvslt"
                        else:
                            il_op = "bvult"
                        il_lhs = expr_map[lhs]
                        il_rhs = expr_map[rhs]
                        # il_op = "bvult"
                        # il_op = fn_map[("<", get_optype(lhs.type))]
                    case ">":
                        if nuxmv.is_integer_type(lhs.type):
                            il_op = ">"
                        elif isinstance(lhs.type, nuxmv.XMVWord) and lhs.type.signed:
                            il_op = "bvsgt"
                        else:
                            il_op = "bvugt"
                        il_lhs = expr_map[lhs]
                        il_rhs = expr_map[rhs]
                        # il_op = "bvugt"
                        # il_op = fn_map[(">", get_optype(lhs.type))]
                    case "<=":
                        if nuxmv.is_integer_type(lhs.type):
                            il_op = "<="
                        elif isinstance(lhs.type, nuxmv.XMVWord) and lhs.type.signed:
                            il_op = "bvsle"
                        else:
                            il_op = "bvule"
                        il_lhs = expr_map[lhs]
                        il_rhs = expr_map[rhs]
                        # il_op = "bvule"
                        # il_op = fn_map[("<=", get_optype(lhs.type))]
                    case ">=":
                        if nuxmv.is_integer_type(lhs.type):
                            il_op = ">="
                        elif isinstance(lhs.type, nuxmv.XMVWord) and lhs.type.signed:
                            il_op = "bvsge"
                        else:
                            il_op = "bvuge"
                        il_lhs = expr_map[lhs]
                        il_rhs = expr_map[rhs]
                        # il_op = "bvuge"
                        # il_op = fn_map[(">=", get_optype(lhs.type))]
                    case "+":
                        il_op = "+" if isinstance(lhs.type, nuxmv.XMVInteger) else "bvadd"
                        il_lhs = expr_map[lhs]
                        il_rhs = expr_map[rhs]
                        # il_op = "bvadd"
                        # il_op = fn_map[("+", get_optype(lhs.type))]
                    case "*":
                        il_op = "*" if isinstance(lhs.type, nuxmv.XMVInteger) else "bvmul"
                        il_lhs = expr_map[lhs]
                        il_rhs = expr_map[rhs]
                        # il_op = "bvmul"
                        # il_op = fn_map[("*", get_optype(lhs.type))]
                    case "/":
                        expr_type = cast(nuxmv.XMVWord, expr.type)
                        il_op = "bvsdiv" if expr_type.signed else "bvudiv"
                        il_lhs = expr_map[lhs]
                        il_rhs = expr_map[rhs]
                    case ">>":
                        if isinstance(lhs.type, nuxmv.XMVWord) and lhs.type.signed:
                            il_op = "bvashr"
                        else:
                            il_op = "bvlshr"
                        il_lhs = expr_map[lhs]
                        il_rhs = expr_map[rhs]
                    case "<<":
                        il_op = "bvshl"
                        il_lhs = expr_map[lhs]
                        il_rhs = expr_map[rhs]
                    case 'mod':
                        if isinstance(lhs.type, nuxmv.XMVWord) and lhs.type.signed:
                            il_op = "bvsrem"
                        else:
                            il_op = "bvurem"
                        il_lhs = expr_map[lhs]
                        il_rhs = expr_map[rhs]
                    case "=" | "<->":
                        il_op = "="
                        try:
                            il_lhs_sort = translate_type(lhs.type, context)
                            if mcil.is_int_sort(il_lhs_sort):
                                il_lhs = expr_map[lhs]
                                il_rhs = expr_map[rhs]
                            else:
                                il_lhs = expr_map[lhs]
                                il_rhs = expr_map[rhs]
                        except ValueError:
                            try:
                                il_rhs_sort = translate_type(rhs.type, context)
                                if mcil.is_int_sort(il_rhs_sort):
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


                expr_map[expr] =  mcil.MCILApply(
                    sort=translate_type(expr.type, context),
                    identifier=mcil.MCILIdentifier(symbol=il_op, indices=[]),
                    children=[il_lhs, il_rhs]
                )
            case nuxmv.XMVUnOp(op=op, arg=arg):
                match op:
                    case "!":
                        il_op = "not" if isinstance(arg.type, nuxmv.XMVBoolean) else "bvnot"
                    case "-":
                        il_op = "-" if isinstance(arg.type, nuxmv.XMVInteger) else "bvneg"
                    case _:
                        il_op = op

                expr_map[expr] =  mcil.MCILApply(
                    sort=translate_type(expr.type, context),
                    identifier=mcil.MCILIdentifier(symbol=il_op, indices=[]),
                    children=[expr_map[arg]]
                )
            case nuxmv.XMVWordBitSelection(word=word, low=low, high=high):
                expr_map[expr] =  mcil.MCILApply(
                    sort=translate_type(expr.type, context),
                    identifier=mcil.MCILIdentifier(symbol="extract", indices=[high, low]),
                    children=[expr_map[word]]
                )
            case nuxmv.XMVCaseExpr():
                expr_map[expr] =  case_to_ite(expr, context, expr_map)
            case nuxmv.XMVModuleAccess(module=ma_module, element=ma_elem):
                expr_map[expr] = mcil.MCILVar(
                    sort=translate_type(expr.type, context),
                    symbol=ma_module.ident + "." + ma_elem.ident,
                    prime=False
                )
            case _:
                raise ValueError(f"unhandled expression {expr}, {expr.__class__}")


def conjoin_list(expr_list: list[mcil.MCILExpr]) -> mcil.MCILExpr:
    if len(expr_list) == 0:
        return mcil.MCIL_BOOL_CONST(True)
    elif len(expr_list) == 1:
        return expr_list[0]
    else:
        return mcil.MCIL_AND_EXPR(expr_list)


def gather_input(xmv_module: nuxmv.XMVModuleDeclaration, context: nuxmv.XMVContext) -> list[tuple[str, mcil.MCILSort]]:
    result: list[tuple[str, mcil.MCILSort]] = []

    for param in xmv_module.parameters:
        # v = mcil.MCILVar(
        #     sort=,
        #     symbol=param.ident, # type: ignore
        #     prime=False
        # )
        result.append((param, translate_type(context.module_params[xmv_module.name][param], context)))

    for module_element in xmv_module.elements:
        match module_element:
            case nuxmv.XMVVarDeclaration(modifier="IVAR"):
                for (var_name, xmv_var_type) in module_element.var_list:
                    if isinstance(xmv_var_type, nuxmv.XMVModuleType):
                        continue

                    result.append((var_name.ident, translate_type(xmv_var_type, context)))
            case _:
                pass
    
    return result


def gather_local(xmv_module: nuxmv.XMVModuleDeclaration, context: nuxmv.XMVContext) -> list[tuple[str, mcil.MCILSort]]:
    result: list[tuple[str, mcil.MCILSort]] = []
    for e in [e for e in xmv_module.elements if isinstance(e, nuxmv.XMVVarDeclaration)]:
        for (var_name, xmv_var_type) in e.var_list: 
            if isinstance(xmv_var_type, nuxmv.XMVModuleType):
                context.module_locals[var_name.ident] = []
                # gathering submodule inputs
                for name in context.module_params[xmv_var_type.module_name]:
                    type = context.module_params[xmv_var_type.module_name][name]
                    input_var = mcil.MCILVar(
                            sort=translate_type(type, context),
                            symbol=var_name.ident + "." + name,
                            prime=False
                        )
                    result.append((var_name.ident + "." + name, translate_type(type, context)))
                    context.module_locals[var_name.ident].append(input_var)

                # gathering submodule outputs
                    
                for (var_symbol, var_sort) in context.outputs[xmv_var_type.module_name]:
                    local_var = mcil.MCILVar(
                        sort=var_sort,
                        symbol=var_name.ident + "." + var_symbol,
                        prime=False
                    )
                    result.append((var_name.ident + "." + var_symbol, var_sort))
                    context.module_locals[var_name.ident].append(local_var)

    return result


def gather_output(xmv_module: nuxmv.XMVModuleDeclaration, context: nuxmv.XMVContext) -> list[tuple[str, mcil.MCILSort]]:
    result: list[tuple[str, mcil.MCILSort]] = []
    
    for module_element in xmv_module.elements:
        match module_element:
            case nuxmv.XMVVarDeclaration(modifier="VAR") | nuxmv.XMVVarDeclaration(modifier="FROZENVAR"):
                for (var_name, xmv_var_type) in module_element.var_list:
                    match xmv_var_type:
                        case nuxmv.XMVEnumeration(summands=summands):
                            if xmv_var_type.is_integer():
                                # values = {int(s) for s in expr.type.summands}
                                # expr.type = nuxmv.XMVInteger(values)
                                il_type = mcil.MCIL_INT_SORT
                            else:
                                lsummands = list(summands)
                                slsummands = [str(s) for s in lsummands]

                                il_symbol = context.reverse_enums[slsummands[0]][0]
                                il_type = mcil.MCIL_ENUM_SORT(il_symbol)
                        case nuxmv.XMVModuleType(module_name=module_name):
                            gather_output(context.modules[module_name], context)
                            continue
                        case _:
                            il_type = translate_type(xmv_var_type, context)

                    result.append((var_name.ident, il_type))
            case nuxmv.XMVDefineDeclaration(define_list=define_list):
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


def specialize_variable(module_name: str, var: mcil.MCILVar) -> mcil.MCILVar:
    return mcil.MCILVar(
        sort=var.sort,
        symbol=module_name + "." + var.symbol,
        prime=var.prime
    )


def specialize_vars_in_expr(module_name: str, expr: mcil.MCILExpr) -> mcil.MCILExpr:
    match expr:
        case mcil.MCILVar():
            return specialize_variable(module_name, expr)
        case mcil.MCILApply(sort=sort, identifier=identifier, children=children):
            schildren = []
            for child in children:
                schildren.append(specialize_vars_in_expr(module_name, child))
            return mcil.MCILApply(sort=sort, identifier=identifier, children=schildren)
        case _:
            return mcil.MCIL_BOOL_CONST(True)
            # print("CATCH ALL CASE:", expr, expr.__class__.__name__)


def gather_init(xmv_module: nuxmv.XMVModuleDeclaration, context: nuxmv.XMVContext, expr_map: dict[nuxmv.XMVExpr, mcil.MCILExpr]) -> mcil.MCILExpr:
    init_list: list[mcil.MCILExpr] = []
    
    for init_decl in [e for e in xmv_module.elements if isinstance(e, nuxmv.XMVInitDeclaration)]:
        translate_expr(init_decl.formula, context, expr_map, in_let_expr=False, module=xmv_module)
        init_list.append(expr_map[init_decl.formula])
    
    for module_element in xmv_module.elements:
        match module_element:
            case nuxmv.XMVAssignDeclaration(assign_list=al):
                for assign_decl in al:
                    if assign_decl.modifier == "init":
                        translate_expr(assign_decl.lhs, context, expr_map, in_let_expr=False, module=xmv_module)
                        translate_expr(assign_decl.rhs, context, expr_map, in_let_expr=False, module=xmv_module)

                        init_expr = mcil.MCIL_EQ_EXPR([expr_map[assign_decl.lhs], 
                                                 expr_map[assign_decl.rhs]])
                        
                        init_list.append(init_expr)
            case _:
                pass

    return conjoin_list(init_list)


def gather_trans(xmv_module: nuxmv.XMVModuleDeclaration, context: nuxmv.XMVContext, expr_map: dict[nuxmv.XMVExpr, mcil.MCILExpr]) -> mcil.MCILExpr:
    trans_list: list[mcil.MCILExpr] = []
    
    for trans_decl in [e for e in xmv_module.elements if isinstance(e, nuxmv.XMVTransDeclaration)]:
        log.debug("translating transition relation", FILE_NAME)
        translate_expr(trans_decl.formula, context, expr_map, in_let_expr=False, module=xmv_module)
        trans_list.append(expr_map[trans_decl.formula])

    for module_element in xmv_module.elements:
        match module_element:
            case nuxmv.XMVAssignDeclaration(assign_list=al):
                for assign_decl in al:
                    if assign_decl.modifier == "next":
                        translate_expr(assign_decl.rhs, context, expr_map, in_let_expr=False, module=xmv_module)

                        if isinstance(assign_decl.lhs, nuxmv.XMVIdentifier):
                            lhs_expr = mcil.MCILVar(
                                        sort=translate_type(assign_decl.rhs.type, context),
                                        symbol=assign_decl.lhs.ident,
                                        prime=True
                                    )
                        else:
                            raise ValueError(f"Unsupported: next(complex_identifier)")

                        trans_expr = mcil.MCIL_EQ_EXPR([lhs_expr, 
                                                  expr_map[assign_decl.rhs]])
                        
                        trans_list.append(trans_expr)
            case _:
                pass

    return conjoin_list(trans_list) if len(trans_list) > 0 else mcil.MCIL_BOOL_CONST(True)


def gather_inv(xmv_module: nuxmv.XMVModuleDeclaration, context: nuxmv.XMVContext, expr_map: dict[nuxmv.XMVExpr, mcil.MCILExpr]) -> mcil.MCILExpr:
    inv_list: list[mcil.MCILExpr] = []
    
    # things marked explicitly as INVAR
    # print("inv - looking for INVAR")
    for inv_decl in [e for e in xmv_module.elements if isinstance(e, nuxmv.XMVInvarDeclaration)]:
        translate_expr(inv_decl.formula, context, expr_map, in_let_expr=False, module=xmv_module)
        inv_list.append(expr_map[inv_decl.formula])

    # standard ASSIGN declarations (without init/next modifiers)
    # print("inv - looking through ASSIGN")
    for module_element in xmv_module.elements:
        match module_element:
            case nuxmv.XMVAssignDeclaration(assign_list=al):
                for assign_decl in al:
                    if assign_decl.modifier == "none":
                        
                        translate_expr(assign_decl.rhs, context, expr_map, in_let_expr=False, module=xmv_module)

                        if isinstance(assign_decl.lhs, nuxmv.XMVIdentifier):
                            lhs_expr = mcil.MCILVar(
                                        sort=translate_type(assign_decl.rhs.type, context),
                                        symbol=assign_decl.lhs.ident,
                                        prime=False
                                    )
                        else:
                            raise ValueError(f"Unsupported: next(complex_identifier)")

                        inv_expr = mcil.MCIL_EQ_EXPR([lhs_expr, expr_map[assign_decl.rhs]])
                        
                        inv_list.append(inv_expr)
            case nuxmv.XMVVarDeclaration(modifier="FROZENVAR", var_list=var_list):
                for (var_name, _) in var_list:
                    var_ident = var_name.ident
                    inv_list.append(mcil.MCIL_EQ_EXPR([
                        mcil.MCILVar(
                            sort=translate_type(context.vars[xmv_module.name][var_ident], context),
                            symbol=var_ident,
                            prime=False
                        ),
                        mcil.MCILVar(
                            sort=translate_type(context.vars[xmv_module.name][var_ident], context),
                            symbol=var_ident,
                            prime=True
                        )
                    ]))
            case nuxmv.XMVVarDeclaration(var_list=var_list):
                # All integer enums must be constrained where they are declared
                # Example: 
                #   var: {0,1,2}
                # should have mcil.MCIL constraint
                #   :inv (and ... (or (= var 0) (= var 1) (= var 2)) ...)
                for (var_name, var_type) in [
                    (var_name, var_type)
                    for (var_name, var_type)
                    in var_list
                    if isinstance(var_type, nuxmv.XMVEnumeration) and var_type.is_integer()
                ]:
                    var_ident = var_name.ident
                    inv_list.append(mcil.MCIL_OR_EXPR([
                        mcil.MCIL_EQ_EXPR([
                            mcil.MCILVar(mcil.MCIL_INT_SORT, var_ident, False),
                            mcil.MCIL_INT_CONST(int(value))
                        ])
                        for value
                        in var_type.summands
                    ]))
                    
            case nuxmv.XMVDefineDeclaration(define_list=define_list):
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
                    inv_list.append(mcil.MCIL_EQ_EXPR([
                        mcil.MCILVar(
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
    for var_list in [vd.var_list for vd in xmv_module.elements if isinstance(vd, nuxmv.XMVVarDeclaration)]:
        for (var_name, var_type) in var_list:
            match var_type:
                case nuxmv.XMVModuleType(module_name=module_name, parameters=parameters):
                    for i, param in enumerate(parameters):
                        # print(f"found parameter {param}")
                        match param:
                            case nuxmv.XMVModuleAccess(module=module, element=elem):
                                # if isinstance(module, nuxmv.XMVModuleAccess):
                                #     module_to_check = module.element
                                # else:
                                #     module_to_check = module.ident

                                mod_typ = context.vars[xmv_module.name][module.ident]
                                source_module = mod_typ.module_name

                                if elem in context.defs[source_module]: # if the module access refers to a def'd element, specialize it and construct expr
                                    translate_expr(context.defs[source_module][elem], context, expr_map, in_let_expr=False, module=context.modules[module_name])
                                    defn = expr_map[context.defs[source_module][elem]]
                                    sdefn = specialize_vars_in_expr(var_name.ident, defn)
                                    init_expr = mcil.MCIL_EQ_EXPR([context.module_locals[var_name.ident][i], sdefn])
                                    inv_list.append(init_expr)
                                else:
                                    translate_expr(param, context, expr_map, in_let_expr=False, module=xmv_module)
                                    init_expr = mcil.MCIL_EQ_EXPR([context.module_locals[var_name.ident][i], expr_map[param]])
                                    inv_list.append(init_expr)
                            case _:
                                translate_expr(param, context, expr_map, in_let_expr=False, module=xmv_module)
                                init_expr = mcil.MCIL_EQ_EXPR([context.module_locals[var_name.ident][i], expr_map[param]])
                                inv_list.append(init_expr)


                case _:
                    pass

    # print("inv - done")
    return conjoin_list(inv_list) if len(inv_list) > 0 else mcil.MCIL_BOOL_CONST(True)

def gather_subsystems(xmv_module: nuxmv.XMVModuleDeclaration, xmv_context: nuxmv.XMVContext) -> dict[str, tuple[str, list[str]]]:
    subsystems: dict[str, tuple[str, list[str]]] = {}

    for e in [e for e in xmv_module.elements if isinstance(e, nuxmv.XMVVarDeclaration)]:
        for (var_name, xmv_var_type) in e.var_list: 
            if isinstance(xmv_var_type, nuxmv.XMVModuleType):
                subsystems[var_name.ident] = (xmv_var_type.module_name,
                                              list(map(lambda x : x.symbol, xmv_context.module_locals[var_name.ident])))

    return subsystems


def gather_consts(xmv_module: nuxmv.XMVModuleDeclaration) -> list[mcil.MCILCommand]:
    return []


def gather_invarspecs(xmv_module: nuxmv.XMVModuleDeclaration, context: nuxmv.XMVContext, expr_map: dict[nuxmv.XMVExpr, mcil.MCILExpr]) -> dict[str, mcil.MCILExpr]:
    invarspec_dict: dict[str, mcil.MCILExpr] = {}

    spec_num = 1
    for invarspec_decl in [e for e in xmv_module.elements if isinstance(e, nuxmv.XMVInvarspecDeclaration)]:
        xmv_expr = invarspec_decl.formula
        translate_expr(xmv_expr, context, expr_map, in_let_expr=False, module=xmv_module)

        invarspec_dict[f"rch_{spec_num}"] = (
            cast(mcil.MCILExpr, mcil.MCILApply(
                mcil.MCIL_BOOL_SORT, 
                mcil.MCILIdentifier("not", []), 
                [expr_map[xmv_expr]]
            )))
            
        spec_num += 1

    return invarspec_dict


def translate_module(xmv_module: nuxmv.XMVModuleDeclaration, context: nuxmv.XMVContext) -> list[mcil.MCILCommand]:
    module_name = xmv_module.name

    log.debug(f"Translating module {module_name}", FILE_NAME)

    log.debug("Translating enums", FILE_NAME)
    # enums = gather_enums(xmv_module, context)

    log.debug("Translating input variables", FILE_NAME)
    input = gather_input(xmv_module, context)

    log.debug("Translating output variables", FILE_NAME)
    output = gather_output(xmv_module, context)

    log.debug("Translating local variables", FILE_NAME)
    local = gather_local(xmv_module, context)

    log.debug("Translating initialization constraints", FILE_NAME)
    emap = {}
    init = gather_init(xmv_module, context, emap)

    log.debug("Translating transition relation", FILE_NAME)
    trans = gather_trans(xmv_module, context, emap)

    log.debug("Translating invariant constraints", FILE_NAME)
    inv = gather_inv(xmv_module, context, emap)

    subsystems = gather_subsystems(xmv_module, context)

    define_system: mcil.MCILCommand = mcil.MCILDefineSystem(
            symbol=xmv_module.name,
            input=input,
            output=output,
            local=local,
            init=init,
            trans=trans,
            inv=inv,
            subsystems=subsystems
        )
    
    reachable: dict[str, mcil.MCILExpr] = gather_invarspecs(xmv_module, context, emap)

    if len(reachable) == 0:
        check_system: list[mcil.MCILCommand] = []
    else:
        check_system: list[mcil.MCILCommand] = [mcil.MCILCheckSystem(
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
    # consts: list[mcil.MCILCommand] = gather_consts(xmv_module)

    return [define_system] + check_system


def infer_logic(commands: list[mcil.MCILCommand]) -> Optional[mcil.MCILSetLogic]:
    for def_sys in [s for s in commands if isinstance(s, mcil.MCILDefineSystem)]:
        variables = def_sys.input + def_sys.output + def_sys.local
        for _,sort in variables:
            if mcil.is_int_sort(sort):
                return mcil.MCILSetLogic(logic="QF_LIA")
            
            # if is_bitvec_sort(sort):
            #     return mcil.MCILSetLogic(logic="QF_ABV")
        
    return mcil.MCILSetLogic(logic="QF_ABV")


def translate(filename: str, xmv_program: nuxmv.XMVProgram) -> Optional[mcil.MCILProgram]:

    log.info("Type checking", FILE_NAME)
    context = nuxmv.XMVContext(filename, xmv_program.modules)
    well_typed = nuxmv.type_check_module(xmv_program.main, context)

    if not well_typed:
        log.error("Failed type checking", FILE_NAME)
        return None

    commands: list[mcil.MCILCommand] = []
    commands += [
        mcil.MCILDeclareEnumSort(symbol, [str(s) for s in enum.summands])
        for symbol,enum
        in context.enums.items()
        if enum.is_symbolic()
    ]
    
    for module in reversed(context.module_dep_order):
        commands += translate_module(xmv_module=module, context=context)

    logic: Optional[mcil.MCILSetLogic] = infer_logic(commands)
    if logic:
        log.debug("inferred SMT logic {logic.logic}", FILE_NAME)
        commands = [logic] + commands

    return mcil.MCILProgram(commands=commands)


def translate_file(
    input_path: pathlib.Path, 
    output_path: pathlib.Path, 
    do_cpp: bool,
    overwrite: bool
) -> int:
    """Parses, type checks, translates, and writes the translation result of `input_path` to `output_path`. Runs C preprocessor if `do_cpp` is True. Returns 0 on success, 1 otherwise."""
    log.info("Parsing", FILE_NAME)
    parse_tree = parse_nuxmv.parse(input_path, do_cpp)
    if not parse_tree:
        log.info(f"Failed parsing specification {input_path}", FILE_NAME)
        return 1

    log.info("Translating", FILE_NAME)
    result = translate(input_path.name, parse_tree)
    if not result:
        log.info(f"Failed translating specification {input_path}", FILE_NAME)
        return 1
    
    if not overwrite and output_path.exists():
        log.error(f"Already exists: {output_path}\n\t"
                  "Did you mean to enable the '--overwrite' option?", FILE_NAME)
        return 1

    log.info(f"Writing output to {output_path}", FILE_NAME)

    with open(str(output_path), "w") as f:
        f.write(str(result))
        log.info(f"Wrote output to {output_path}", FILE_NAME)

    return 0