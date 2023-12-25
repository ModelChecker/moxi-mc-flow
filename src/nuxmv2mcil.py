from pathlib import Path
from typing import Tuple, cast

from .util import eprint # type: ignore
from .preprocess_nuxmv import preprocess
from .parse_nuxmv import parse
from .nuxmv import *
from .mcil import *

FILE_NAME = Path(__file__).name

def translate_type(xmv_type: XMVType) -> MCILSort:
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
            return MCIL_BITVEC_SORT(w)
        case XMVArray(type=t):
            return MCIL_ARRAY_SORT(MCIL_INT_SORT, translate_type(t))
        case XMVWordArray(word_length=wl, type=t):
            return MCIL_ARRAY_SORT(MCIL_BITVEC_SORT(wl), translate_type(t))
        case _:
            raise ValueError(f"Unsupported type: {xmv_type}")
        
def coerce_int_to_bv(expr: MCILExpr) -> MCILExpr:
    if isinstance(expr, MCILConstant) and is_int_sort(expr.sort):
        return MCILConstant(
            MCIL_BITVEC_SORT(len(bin(expr.value)[2:])), 
            expr.value
        )
    return expr

def case_to_ite(case_expr: XMVCaseExpr, context: XMVContext) -> MCILExpr:
    """Recursively translate a case expression to a series of cascaded ite expressions."""

    def _case_to_ite(branches: list[tuple[XMVExpr, XMVExpr]], i: int) -> MCILExpr:
        (cond, branch) = branches[i]

        if i >= len(branches)-1:
            return MCILApply(
                translate_type(branch.type),
                MCILIdentifier("ite", []),
                [
                    context.expr_map[cond],
                    context.expr_map[branch],
                    context.expr_map[branch]
                ]
            ) 

        return MCILApply(
            translate_type(branch.type),
            MCILIdentifier("ite", []),
            [
                context.expr_map[cond],
                context.expr_map[branch],
                _case_to_ite(branches, i+1)
            ]
        )

    return _case_to_ite(case_expr.branches, 0)

def translate_expr(xmv_expr: XMVExpr, context: XMVContext) -> None:

    def _translate_expr(expr: XMVExpr):
        nonlocal context

        if expr in context.expr_map:
            return

        match expr:
            case XMVIdentifier(ident=ident):
                if ident in context.defs:
                    context.expr_map[expr] = context.expr_map[context.defs[ident]]
                    # if ident in context.seen_defs:
                    #     raise ValueError(f"Circular definition, detected at `{expr}`")

                    # context.seen_defs.append(ident)
                    # if ident in translated: # cache translated expressions
                    #     context.seen_defs.pop()
                    #     return translated[ident]
                    # else:
                    #     ret = translate_expr(context.defs[ident], context)
                    #     translated[ident] = ret
                    #     context.seen_defs.pop()
                    #     return ret
                elif ident in context.vars:
                    context.expr_map[expr] =  MCILVar(
                        var_type=MCILVarType.INPUT,
                        sort=translate_type(context.vars[ident]),
                        symbol=ident,
                        prime=False
                    )
                else:
                    raise ValueError(f"Unrecognized var `{ident}`")
            case XMVIntegerConstant(integer=i):
                context.expr_map[expr] =  MCILConstant(sort=MCIL_INT_SORT, value=i)
            case XMVBooleanConstant(boolean=b):
                context.expr_map[expr] =  MCILConstant(sort=MCIL_BOOL_SORT, value=b)
            case XMVWordConstant(width=width, value=value):
                context.expr_map[expr] =  MCILConstant(
                    sort=MCIL_BITVEC_SORT(width), 
                    value=int(value)
                )            
            case XMVFunCall(name=fname, args=fargs):
                match fname:
                    case "signed":
                        context.expr_map[expr] = context.expr_map[fargs[0]]
                    case "unsigned":
                        context.expr_map[expr] = context.expr_map[fargs[0]]
                    case "next":
                        match fargs[0]:
                            case XMVIdentifier(ident=ident):
                                context.expr_map[expr] =  MCILVar(
                                    var_type=MCILVarType.LOCAL,
                                    sort=translate_type(context.vars[ident]),
                                    symbol=ident,
                                    prime=True
                                )
                            case _:
                                raise ValueError("complex next expressions unsupported")
                        
                    case _:
                        context.expr_map[expr] =  MCILApply(
                            sort=MCIL_NO_SORT,
                            identifier=MCILIdentifier(symbol=fname, indices=[]),
                            children=[context.expr_map[arg] for arg in fargs]
                        )
            case XMVBinOp(op=op, lhs=lhs, rhs=rhs):
                match op:
                    case '&':
                        il_op = "and" if isinstance(lhs.type, XMVBoolean) else "bvand"
                        il_lhs = context.expr_map[lhs]
                        il_rhs = context.expr_map[rhs]
                    case '|':
                        il_op = "or" if isinstance(lhs.type, XMVBoolean) else "bvor"
                        il_lhs = context.expr_map[lhs]
                        il_rhs = context.expr_map[rhs]
                    case 'xor':
                        il_op = "xor" if isinstance(lhs.type, XMVBoolean) else "bvxor"
                        il_lhs = context.expr_map[lhs]
                        il_rhs = context.expr_map[rhs]
                    case "->":
                        il_op = "=>"
                        il_lhs = context.expr_map[lhs]
                        il_rhs = context.expr_map[rhs]
                    case "!=":
                        il_op = "distinct"
                        il_lhs = context.expr_map[lhs]
                        il_rhs = context.expr_map[rhs]
                    case "<":
                        il_op = "bvult"
                        il_lhs = coerce_int_to_bv(context.expr_map[lhs])
                        il_rhs = coerce_int_to_bv(context.expr_map[rhs])
                    case "+":
                        il_op = "bvadd"
                        il_lhs = coerce_int_to_bv(context.expr_map[lhs])
                        il_rhs = coerce_int_to_bv(context.expr_map[rhs])
                    case "*":
                        il_op = "bvmul"
                        il_lhs = coerce_int_to_bv(context.expr_map[lhs])
                        il_rhs = coerce_int_to_bv(context.expr_map[rhs])
                    case "/":
                        expr_type = cast(XMVWord, expr.type)
                        il_op = "bvsdiv" if expr_type.signed else "bvudiv"
                        il_lhs = coerce_int_to_bv(context.expr_map[lhs])
                        il_rhs = coerce_int_to_bv(context.expr_map[rhs])
                    case ">>":
                        il_op = "bvashr"
                        il_lhs = context.expr_map[lhs]
                        il_rhs = context.expr_map[rhs]
                    case "<<":
                        il_op = "bvshl"
                        il_lhs = context.expr_map[lhs]
                        il_rhs = context.expr_map[rhs]
                    case 'mod':
                        il_op = "bvsmod"
                        il_lhs = context.expr_map[lhs]
                        il_rhs = context.expr_map[rhs]
                    case "=" | "<->":
                        il_op = "="
                        try:
                            il_lhs_sort = translate_type(lhs.type)
                            if is_int_sort(il_lhs_sort):
                                il_lhs = coerce_int_to_bv(context.expr_map[lhs])
                                il_rhs = context.expr_map[rhs]
                            else:
                                il_lhs = context.expr_map[lhs]
                                il_rhs = context.expr_map[rhs]
                        except ValueError:
                            try:
                                il_rhs_sort = translate_type(rhs.type)
                                if is_int_sort(il_rhs_sort):
                                    il_rhs = coerce_int_to_bv(context.expr_map[rhs])
                                    il_lhs = context.expr_map[lhs]
                                else:
                                    il_lhs = context.expr_map[lhs]
                                    il_rhs = context.expr_map[rhs]
                            except ValueError:
                                il_lhs = context.expr_map[lhs]
                                il_rhs = context.expr_map[rhs]
                    case _:
                        il_op = op
                        il_lhs = context.expr_map[lhs]
                        il_rhs = context.expr_map[rhs]


                context.expr_map[expr] =  MCILApply(
                    sort=translate_type(expr.type),
                    identifier=MCILIdentifier(symbol=il_op, indices=[]),
                    children=[il_lhs, il_rhs]
                )
            case XMVUnOp(op=op, arg=arg):
                match op:
                    case "!":
                        il_op = "not" if isinstance(arg.type, XMVBoolean) else "bvnot"
                    case "-":
                        il_op = "bvneg"
                    case _:
                        il_op = op

                context.expr_map[expr] =  MCILApply(
                    sort=translate_type(expr.type),
                    identifier=MCILIdentifier(symbol=il_op, indices=[]),
                    children=[context.expr_map[arg]]
                )
            case XMVWordBitSelection(word=word, low=low, high=high):
                context.expr_map[expr] =  MCILApply(
                    sort=translate_type(expr.type),
                    identifier=MCILIdentifier(symbol="extract", indices=[high, low]),
                    children=[context.expr_map[word]]
                )
            case XMVCaseExpr():
                context.expr_map[expr] =  case_to_ite(expr, context)
            case XMVModuleAccess():
                raise ValueError(f"[{FILE_NAME}] module access")
            case _:
                raise ValueError(f"[{FILE_NAME}] unhandled expression {expr}, {expr.__class__}")
        
    for subexpr in postorder_nuxmv(xmv_expr, context):
        _translate_expr(subexpr)

def conjoin_list(expr_list: list[MCILExpr]) -> MCILExpr:
    if len(expr_list) == 1:
        return expr_list[0]
    else:
        head, *tail = expr_list
        and_ident: MCILIdentifier = MCILIdentifier(symbol="and", indices=[])
        return MCILApply(
            sort=MCIL_BOOL_SORT,
            identifier=and_ident,
            children=[head, conjoin_list(tail)]
        )

def disjoin_list(expr_list: list[MCILExpr]) -> MCILExpr:
    if len(expr_list) == 1:
        return expr_list[0]
    else:
        head, *tail = expr_list
        and_ident: MCILIdentifier = MCILIdentifier(symbol="or", indices=[])
        return MCILApply(
            sort=MCIL_BOOL_SORT,
            identifier=and_ident,
            children=[head, disjoin_list(tail)]
        )

def gather_input(xmv_module: XMVModule, context: XMVContext) -> list[MCILVar]:
    result: list[MCILVar] = []
    for module_element in xmv_module.elements:
        match module_element:
            case XMVVarDeclaration(modifier="IVAR"):
                for (var_name, xmv_var_type) in module_element.var_list:
                    if isinstance(xmv_var_type, XMVModuleType):
                        continue

                    mcil_var = MCILVar(
                        var_type=MCILVarType.INPUT,
                        sort=translate_type(xmv_var_type),
                        symbol=var_name.ident,
                        prime=False
                    )

                    result.append(mcil_var)
            case _:
                pass
    
    return result

def gather_local(xmv_module: XMVModule, context: XMVContext) -> list[MCILVar]:
    return []

def gather_output(xmv_module: XMVModule, context: XMVContext) -> list[MCILVar]:
    result: list[MCILVar] = []
    for module_element in xmv_module.elements:
        match module_element:
            case XMVVarDeclaration(modifier="VAR") | XMVVarDeclaration(modifier="FROZENVAR"):
                for (var_name, xmv_var_type) in module_element.var_list:
                    match xmv_var_type:
                        case XMVEnumeration(summands=summands):
                            lsummands = list(summands)
                            slsummands = [str(s) for s in lsummands]
                            
                            il_symbol = context.reverse_enums[slsummands[0]]
                            il_type = MCIL_ENUM_SORT(il_symbol)
                        case _:
                            il_type = translate_type(xmv_var_type)

                    mcil_var = MCILVar(
                        var_type=MCILVarType.OUTPUT,
                        sort=il_type,
                        symbol=var_name.ident,
                        prime=False
                    )

                    result.append(mcil_var)
            case _:
               pass
    
    return result

def gather_init(xmv_module: XMVModule, context: XMVContext) -> MCILExpr:
    init_list: list[MCILExpr] = []
    
    for init_decl in [e for e in xmv_module.elements if isinstance(e, XMVInitDeclaration)]:
        translate_expr(init_decl.formula, context)
        init_list.append(context.expr_map[init_decl.formula])
    
    for module_element in xmv_module.elements:
        match module_element:
            case XMVAssignDeclaration(assign_list=al):
                for assign_decl in al:
                    if assign_decl.modifier == "init":
                        translate_expr(assign_decl.lhs, context)
                        translate_expr(assign_decl.rhs, context)

                        init_expr = MCIL_EQ_EXPR(context.expr_map[assign_decl.lhs], 
                                                 context.expr_map[assign_decl.rhs])
                        
                        init_list.append(init_expr)
            case _:
                pass

    return conjoin_list(init_list) if len(init_list) > 0 else MCIL_BOOL_EXPR(True)

def gather_trans(xmv_module: XMVModule, context: XMVContext) -> MCILExpr:
    trans_list: list[MCILExpr] = []
    
    for trans_decl in [e for e in xmv_module.elements if isinstance(e, XMVTransDeclaration)]:
        translate_expr(trans_decl.formula, context)
        trans_list.append(context.expr_map[trans_decl.formula])

    for module_element in xmv_module.elements:
        match module_element:
            case XMVAssignDeclaration(assign_list=al):
                for assign_decl in al:
                    if assign_decl.modifier == "next":
                        translate_expr(assign_decl.rhs, context)

                        if isinstance(assign_decl.lhs, XMVIdentifier):
                            lhs_expr = MCILVar(
                                        var_type=MCILVarType.LOCAL,
                                        sort=translate_type(assign_decl.rhs.type),
                                        symbol=assign_decl.lhs.ident,
                                        prime=True
                                    )
                        else:
                            raise ValueError(f"Unsupported: next(complex_identifier)")

                        trans_expr = MCIL_EQ_EXPR(lhs_expr, 
                                                  context.expr_map[assign_decl.rhs])
                        
                        trans_list.append(trans_expr)
            case _:
                pass

    return conjoin_list(trans_list) if len(trans_list) > 0 else MCIL_BOOL_EXPR(True)

def gather_inv(xmv_module: XMVModule, context: XMVContext) -> MCILExpr:
    inv_list: list[MCILExpr] = []
    
    for inv_decl in [e for e in xmv_module.elements if isinstance(e, XMVInvarDeclaration)]:
        translate_expr(inv_decl.formula, context)
        inv_list.append(context.expr_map[inv_decl.formula])
    
    for module_element in xmv_module.elements:
        match module_element:
            case XMVVarDeclaration(modifier="FROZENVAR", var_list=var_list):
                for (var_name, _) in var_list:
                    var_ident = var_name.ident
                    inv_list.append(MCIL_EQ_EXPR(
                        MCILVar(
                            var_type=MCILVarType.OUTPUT,
                            sort=translate_type(context.vars[var_ident]),
                            symbol=var_ident,
                            prime=False
                        ),
                        MCILVar(
                            var_type=MCILVarType.OUTPUT,
                            sort=translate_type(context.vars[var_ident]),
                            symbol=var_ident,
                            prime=True
                        )
                    ))
            # TODO: nuXmv calls out anything in the DEFINE section as
            # just a macro...we treat it the same way
            # This does have some implications for how we handle module 
            # accesses -- for something like `module.def`, we replace with
            # the equivalent expression using the input/outputs for the
            # `module` subsystem declaration
            # case XMVDefineDeclaration(define_list=define_list):
            #     for define in define_list:
            #         inv_list.append(MCIL_EQ_EXPR(
            #             translate_expr(define.name, context), 
            #             translate_expr(define.expr, context)
            #         ))
            case _:
               pass

    return conjoin_list(inv_list) if len(inv_list) > 0 else MCIL_BOOL_EXPR(True)

def gather_subsystems(xmv_module: XMVModule) -> dict[str, tuple[str, list[str]]]:
    return {}

counter = 0
def gensym(st: str):
    global counter
    counter += 1
    return st + str(counter)

def gather_enums(xmv_module: XMVModule, xmv_context: XMVContext) -> Tuple[list[MCILCommand], XMVContext]:
    ret: list[MCILCommand] = []
    for var in xmv_context.vars:
        xmv_type: XMVType = xmv_context.vars[var]
        match xmv_type:
            case XMVEnumeration(summands=summands):
                new_sym: str = gensym("enum")
                set_list: list[str|int] = list(summands)
                str_set_list: list[str] = [str(s) for s in set_list]
                cmd: MCILCommand = MCILDeclareEnumSort(symbol=new_sym, values=str_set_list)
                ret.append(cmd)
                for st in str_set_list:
                    xmv_context.reverse_enums[st] = new_sym
            case _:
                pass
    return (ret, xmv_context)

def gather_consts(xmv_module: XMVModule) -> list[MCILCommand]:
    return []

def gather_invarspecs(xmv_module: XMVModule, context: XMVContext) -> dict[str, MCILExpr]:
    invarspec_dict: dict[str, MCILExpr] = {}

    for invarspec_decl in [e for e in xmv_module.elements if isinstance(e, XMVInvarspecDeclaration)]:
        xmv_expr = invarspec_decl.formula
        translate_expr(xmv_expr, context)

        invarspec_dict[f"rch_{repr(xmv_expr).replace(' ','_')}"] = (
            cast(MCILExpr, MCILApply(
                MCIL_BOOL_SORT, 
                MCILIdentifier("not", []), 
                [context.expr_map[xmv_expr]]
            )))

    return invarspec_dict

def translate_module(xmv_module: XMVModule) -> list[MCILCommand]:
    print(f"[{FILE_NAME}] translating module {xmv_module.name}")

    print(f"[{FILE_NAME}] type checking")
    (_, enum_context) = type_check_enums(xmv_module, XMVContext())
    (type_correct, enum_context) = type_check(xmv_module, enum_context)
    if not type_correct:
        raise ValueError("Not type correct")
    
    enums, updated_enum_context = gather_enums(xmv_module, enum_context)
    xmv_context = updated_enum_context

    print(f"[{FILE_NAME}] translating input variables")
    input = gather_input(xmv_module, xmv_context)

    print(f"[{FILE_NAME}] translating output variables")
    output = gather_output(xmv_module, xmv_context)

    # local = gather_local(xmv_module, xmv_context)
    # print(f"[{FILE_NAME}] translated specification in {input_path}")

    print(f"[{FILE_NAME}] translating initialization constraints")
    init = gather_init(xmv_module, xmv_context)

    print(f"[{FILE_NAME}] translating transition relation")
    trans = gather_trans(xmv_module, xmv_context)

    print(f"[{FILE_NAME}] translating invariant constraints")
    inv = gather_inv(xmv_module, xmv_context)

    subsystems = gather_subsystems(xmv_module)

    define_system: MCILCommand = MCILDefineSystem(
            symbol=xmv_module.name,
            input=input,
            output=output,
            local=[],
            init=init,
            trans=trans,
            inv=inv,
            subsystems=subsystems
        )
    
    reachable: dict[str, MCILExpr] = gather_invarspecs(xmv_module, xmv_context)

    if len(reachable) == 0:
        check_system: list[MCILCommand] = []
    else:
        check_system: list[MCILCommand] = [MCILCheckSystem(
                sys_symbol=xmv_module.name,
                input=input,
                output=output,
                local=[],
                assumption={},
                fairness={},
                reachable=reachable,
                current={},
                query={f"qry_{r}":[r] for r in reachable.keys()},
            )]

    # commands
    consts: list[MCILCommand] = gather_consts(xmv_module)

    return enums + consts + [define_system] + check_system


def translate(xmv_specification: XMVSpecification) -> Optional[MCILProgram]:
    commands: list[MCILCommand] = []
    for xmv_module in xmv_specification.modules:
        try:
            il_commands = translate_module(xmv_module=xmv_module)
        except ValueError as err:
            eprint(err)
            return None
            
        commands += il_commands

    return MCILProgram(commands=commands)

def main(input_path: Path, output_path: Path, do_sort_check: bool) -> int:
    content = preprocess(input_path)

    print(f"[{FILE_NAME}] parsing specification in {input_path}")
    parse_tree = parse(content)
    if not parse_tree:
        eprint(f"[{FILE_NAME}] failed parsing specification in {input_path}")
        return 1

    print(f"[{FILE_NAME}] translating specification in {input_path}")
    result = translate(parse_tree)
    if not result:
        eprint(f"[{FILE_NAME}] failed translating specification in {input_path}")
        return 1

    print(f"[{FILE_NAME}] writing output to {output_path}")
    with open(str(output_path), "w") as f:
        f.write(str(result))
        print(f"[{FILE_NAME}] wrote output to {output_path}")

    print(f"[{FILE_NAME}] sort checking translated output")
    if do_sort_check:
        (well_sorted, _) = sort_check(result)
        if not well_sorted:
            eprint(f"[{FILE_NAME}] failed sort checking translated specification in {input_path}")
            return 1

    return 0
    print(f"[{FILE_NAME}] translated invariant constraints")

# if __name__ == '__main__':
#     argparser = argparse.ArgumentParser(
#                            prog='nuXmv/NuSMV to IL translation',
#                            description='Parses a nuXmv/NuSMV (.smv) file and translates the resulting AST into IL'
#    )
#     argparser.add_argument("input", help="source nuXmv program to translate")
#     argparser.add_argument("--output", help="path of output file")
#     argparser.add_argument("--sort-check", action="store_true", help="enable sort checking")

#     args = argparser.parse_args()
#     input_path = Path(args.input)
#     output_path = Path(args.output) if args.output else Path(input_path).with_suffix('.mcil')

#     main(input_path, output_path, args.sort_check)