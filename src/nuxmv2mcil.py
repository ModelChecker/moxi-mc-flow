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
    """Recursively translate a case expression to a series of cascaded ite expressions. FIXME: I think this might not be correct, might get stuck in infinite loop on some examples"""

    def _case_to_ite(branches: list[tuple[XMVExpr, XMVExpr]], i: int) -> MCILExpr:
        (cond, branch) = branches[i]

        if i >= len(branches)-1:
            return MCILApply(
                translate_type(branch.type),
                MCILIdentifier("ite", []),
                [
                    translate_expr(cond, context),
                    translate_expr(branch, context),
                    translate_expr(branch, context)
                ]
            ) 

        return MCILApply(
            translate_type(branch.type),
            MCILIdentifier("ite", []),
            [
                translate_expr(cond, context),
                translate_expr(branch, context),
                _case_to_ite(branches, i+1)
            ]
        )

    return _case_to_ite(case_expr.branches, 0)

translated: dict[str, MCILExpr] = {}

def translate_expr(xmv_expr: XMVExpr, context: XMVContext) -> MCILExpr:
    match xmv_expr:
        case XMVIdentifier(ident=ident):
            if ident in context.defs:
                if ident in context.seen_defs:
                    print(context.seen_defs)
                    raise ValueError(f"Circular definition, detected at `{xmv_expr}`")

                context.seen_defs.append(ident)
                if ident in translated: # cache translated expressions
                    context.seen_defs.pop()
                    return translated[ident]
                else:
                    ret = translate_expr(context.defs[ident], context)
                    translated[ident] = ret
                    context.seen_defs.pop()
                    return ret
            elif ident in context.vars:
                return MCILVar(
                    var_type=MCILVarType.INPUT,
                    sort=translate_type(context.vars[ident]),
                    symbol=ident,
                    prime=False
                )
            else:
                raise ValueError(f"Unrecognized var `{ident}`")
        case XMVIntegerConstant(integer=i):
            return MCILConstant(sort=MCIL_INT_SORT, value=i)
        case XMVBooleanConstant(boolean=b):
            return MCILConstant(sort=MCIL_BOOL_SORT, value=b)
        case XMVWordConstant(width=width, value=value):
            return MCILConstant(
                sort=MCIL_BITVEC_SORT(width), 
                value=int(value)
            )            
        case XMVFunCall(name=fname, args=fargs):
            match fname:
                case "signed":
                    return translate_expr(fargs[0], context)
                case "unsigned":
                    return translate_expr(fargs[0], context)
                case "next":
                    match fargs[0]:
                        case XMVIdentifier(ident=ident):
                            return MCILVar(
                                var_type=MCILVarType.LOCAL,
                                sort=translate_type(context.vars[ident]),
                                symbol=ident,
                                prime=True
                            )
                        case _:
                            raise ValueError("complex next expressions unsupported")
                    
                case _:
                    return MCILApply(
                        sort=MCIL_NO_SORT,
                        identifier=MCILIdentifier(symbol=fname, indices=[]),
                        children=[translate_expr(e, context) for e in fargs]
                    )
        case XMVBinOp(op=op, lhs=lhs, rhs=rhs):
            match op:
                case '&':
                    il_op = "and" if isinstance(lhs.type, XMVBoolean) else "bvand"
                    il_lhs = translate_expr(lhs, context)
                    il_rhs = translate_expr(rhs, context)
                case '|':
                    il_op = "or" if isinstance(lhs.type, XMVBoolean) else "bvor"
                    il_lhs = translate_expr(lhs, context)
                    il_rhs = translate_expr(rhs, context)
                case 'xor':
                    il_op = "xor" if isinstance(lhs.type, XMVBoolean) else "bvxor"
                    il_lhs = translate_expr(lhs, context)
                    il_rhs = translate_expr(rhs, context)
                case "->":
                    il_op = "=>"
                    il_lhs = translate_expr(lhs, context)
                    il_rhs = translate_expr(rhs, context)
                case "!=":
                    il_op = "distinct"
                    il_lhs = translate_expr(lhs, context)
                    il_rhs = translate_expr(rhs, context)
                case "<":
                    il_op = "bvult"
                    il_lhs = coerce_int_to_bv(translate_expr(lhs, context))
                    il_rhs = coerce_int_to_bv(translate_expr(rhs, context))
                case "+":
                    il_op = "bvadd"
                    il_lhs = coerce_int_to_bv(translate_expr(lhs, context))
                    il_rhs = coerce_int_to_bv(translate_expr(rhs, context))
                case "*":
                    il_op = "bvmul"
                    il_lhs = coerce_int_to_bv(translate_expr(lhs, context))
                    il_rhs = coerce_int_to_bv(translate_expr(rhs, context))
                case "/":
                    expr_type = cast(XMVWord, xmv_expr.type)
                    il_op = "bvsdiv" if expr_type.signed else "bvudiv"
                    il_lhs = coerce_int_to_bv(translate_expr(lhs, context))
                    il_rhs = coerce_int_to_bv(translate_expr(rhs, context))
                case ">>":
                    il_op = "bvashr"
                    il_lhs = translate_expr(lhs, context)
                    il_rhs = translate_expr(rhs, context)
                case "<<":
                    il_op = "bvshl"
                    il_lhs = translate_expr(lhs, context)
                    il_rhs = translate_expr(rhs, context)
                case 'mod':
                    il_op = "bvsmod"
                    il_lhs = translate_expr(lhs, context)
                    il_rhs = translate_expr(rhs, context)
                case "=" | "<->":
                    il_op = "="
                    try:
                        il_lhs_sort = translate_type(lhs.type)
                        if is_int_sort(il_lhs_sort):
                            il_lhs = coerce_int_to_bv(translate_expr(lhs, context))
                            il_rhs = translate_expr(rhs, context)
                        else:
                            il_lhs = translate_expr(lhs, context)
                            il_rhs = translate_expr(rhs, context)
                    except ValueError:
                        try:
                            il_rhs_sort = translate_type(rhs.type)
                            if is_int_sort(il_rhs_sort):
                                il_rhs = coerce_int_to_bv(translate_expr(rhs, context))
                                il_lhs = translate_expr(lhs, context)
                            else:
                                il_lhs = translate_expr(lhs, context)
                                il_rhs = translate_expr(rhs, context)
                        except ValueError:
                            il_lhs = translate_expr(lhs, context)
                            il_rhs = translate_expr(rhs, context)
                case _:
                    il_op = op
                    il_lhs = translate_expr(lhs, context)
                    il_rhs = translate_expr(rhs, context)


            return MCILApply(
                sort=translate_type(xmv_expr.type),
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

            return MCILApply(
                sort=translate_type(xmv_expr.type),
                identifier=MCILIdentifier(symbol=il_op, indices=[]),
                children=[translate_expr(arg, context)]
            )
        case XMVWordBitSelection(word=word, low=low, high=high):
            return MCILApply(
                sort=translate_type(xmv_expr.type),
                identifier=MCILIdentifier(symbol="extract", indices=[high, low]),
                children=[translate_expr(word, context)]
            )
        case XMVCaseExpr():
            return case_to_ite(xmv_expr, context)
        case XMVModuleAccess():
            raise ValueError(f"[{FILE_NAME}] module access")
        case _:
            raise ValueError(f"[{FILE_NAME}] unhandled expression {xmv_expr}, {xmv_expr.__class__}")

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
    init_list = [translate_expr(e.formula, context) for e in xmv_module.elements if isinstance(e, XMVInitDeclaration)]

    return conjoin_list(init_list) if len(init_list) > 0 else MCIL_BOOL_EXPR(True)

def gather_trans(xmv_module: XMVModule, context: XMVContext) -> MCILExpr:
    trans_list = [translate_expr(e.formula, context) for e in xmv_module.elements if isinstance(e, XMVTransDeclaration)]

    return disjoin_list(trans_list) if len(trans_list) > 0 else MCIL_BOOL_EXPR(True)

def gather_inv(xmv_module: XMVModule, context: XMVContext) -> MCILExpr:
    inv_list = [translate_expr(e.formula, context) for e in xmv_module.elements if isinstance(e, XMVInvarDeclaration)]
    
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
    invarspec_dict = {
        f"rch_{repr(e.formula).replace(' ','_')}": 
                cast(MCILExpr, MCILApply(
                    MCIL_BOOL_SORT, 
                    MCILIdentifier("not", []), 
                    [translate_expr(e.formula, context)]
                ))
        for e in xmv_module.elements if isinstance(e, XMVInvarspecDeclaration)}

    return invarspec_dict

def translate_module(xmv_module: XMVModule) -> list[MCILCommand]:
    print(f"[{FILE_NAME}] translating module {xmv_module.name}")

    (_, enum_context) = type_check_enums(xmv_module, XMVContext())
    (type_correct, enum_context) = type_check(xmv_module, enum_context)
    if not type_correct:
        raise ValueError("Not type correct")
    
    enums, updated_enum_context = gather_enums(xmv_module, enum_context)
    xmv_context = updated_enum_context

    input = gather_input(xmv_module, xmv_context)
    output = gather_output(xmv_module, xmv_context)
    local = gather_local(xmv_module, xmv_context)

    init = gather_init(xmv_module, xmv_context)
    trans = gather_trans(xmv_module, xmv_context)
    inv = gather_inv(xmv_module, xmv_context)

    subsystems = gather_subsystems(xmv_module)

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
    
    reachable: dict[str, MCILExpr] = gather_invarspecs(xmv_module, xmv_context)

    if len(reachable) == 0:
        check_system: list[MCILCommand] = []
    else:
        check_system: list[MCILCommand] = [MCILCheckSystem(
                sys_symbol=xmv_module.name,
                input=input,
                output=output,
                local=local,
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

    parse_tree = parse(content)
    if not parse_tree:
        eprint(f"[{FILE_NAME}] failed parsing specification in {input_path}")
        return 1
    print(f"[{FILE_NAME}] parsed specification in {input_path}")

    result = translate(parse_tree)
    if not result:
        eprint(f"[{FILE_NAME}] failed translating specification in {input_path}")
        return 1

    with open(str(output_path), "w") as f:
        f.write(str(result))
        print(f"[{FILE_NAME}] wrote output to {output_path}")

    if do_sort_check:
        (well_sorted, _) = sort_check(result)
        if not well_sorted:
            eprint(f"[{FILE_NAME}] failed sort checking translated specification in {input_path}")
            return 1

    return 0

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