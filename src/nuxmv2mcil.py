import argparse
from pathlib import Path
from parse_nuxmv import parse
from nuxmv import *
from mcil import *

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
        case XMVEnumeration(summands=s):
            return MCIL_ENUM_SORT(s[0])
        case XMVRange():
            raise ValueError("not in mcil.py AST?")
        case XMVArray(type=t):
            return MCIL_ARRAY_SORT(MCIL_INT_SORT, translate_type(t))
        case _:
            raise ValueError(f"Unidentified type: {xmv_type}")
        
def coerce_int_to_bv(expr: MCILExpr) -> MCILExpr:
    match expr:
        case MCILConstant(sort=MCIL_INT_SORT, value=v):
            return MCILConstant(sort=MCIL_BITVEC_SORT(len(bin(v)[2:])), value=v)
        case _:
            return expr

def translate_expr(xmv_expr: XMVExpr) -> MCILExpr:
    match xmv_expr:
        case XMVIdentifier(ident=i):
            return MCILVar(
                var_type=MCILVarType.LOCAL,
                sort=MCIL_BOOL_SORT, # TODO
                symbol=i,
                prime=False
            )
        case XMVIntegerConstant(integer=i):
            return MCILConstant(sort=MCIL_INT_SORT, value=i)
        case XMVBooleanConstant(boolean=b):
            return MCILConstant(sort=MCIL_BOOL_SORT, value=b)
        case XMVWordConstant():
            return MCILConstant(
                sort=MCIL_BITVEC_SORT(xmv_expr.width), 
                value=int(xmv_expr.value)
            )            
        case XMVFunCall(function_name=fname, function_args=fargs):
            match fname:
                case "signed":
                    return translate_expr(fargs[0])
                case "unsigned":
                    return translate_expr(fargs[0])
                case "next":
                    match fargs[0]:
                        case XMVIdentifier(ident=i):
                            return MCILVar(
                                var_type=MCILVarType.LOCAL,
                                sort=MCIL_BOOL_SORT, # TODO
                                symbol=fargs[0].ident,
                                prime=True
                            )
                        case _:
                            raise ValueError("complex next expressions unsupported")
                    
                case _:
                    return MCILApply(
                        sort=MCIL_NO_SORT,
                        identifier=MCILIdentifier(symbol=fname, indices=[]),
                        children=[translate_expr(e) for e in fargs]
                    )
        case XMVBinop(op=op, lhs=lhs, rhs=rhs):
            match op:
                case '&':
                    il_op = "and"
                    il_lhs = translate_expr(lhs)
                    il_rhs = translate_expr(rhs)
                case '|':
                    il_op = "or"
                    il_lhs = translate_expr(lhs)
                    il_rhs = translate_expr(rhs)
                case '!':
                    il_op = "not"
                    il_lhs = translate_expr(lhs)
                    il_rhs = translate_expr(rhs)
                case "->":
                    il_op = "=>"
                    il_lhs = translate_expr(lhs)
                    il_rhs = translate_expr(rhs)
                case "!=":
                    il_op = "distinct"
                    il_lhs = translate_expr(lhs)
                    il_rhs = translate_expr(rhs)
                case "<":
                    il_op = "bvult"
                    il_lhs = coerce_int_to_bv(translate_expr(lhs))
                    il_rhs = coerce_int_to_bv(translate_expr(rhs))
                case "+":
                    il_op = "bvadd"
                    il_lhs = coerce_int_to_bv(translate_expr(lhs))
                    il_rhs = coerce_int_to_bv(translate_expr(rhs))
                case "=":
                    il_op = "="
                    try:
                        il_lhs_sort = synthesize_sort(lhs)
                        if is_int_sort(il_lhs_sort):
                            il_lhs = coerce_int_to_bv(translate_expr(lhs))
                            il_rhs = translate_expr(rhs)
                        else:
                            il_lhs = translate_expr(lhs)
                            il_rhs = translate_expr(rhs)
                    except ValueError:
                        try:
                            il_rhs_sort = synthesize_sort(rhs)
                            if is_int_sort(il_rhs_sort):
                                il_rhs = coerce_int_to_bv(translate_expr(rhs))
                                il_lhs = translate_expr(lhs)
                            else:
                                il_lhs = translate_expr(lhs)
                                il_rhs = translate_expr(rhs)
                        except ValueError:
                            il_lhs = translate_expr(lhs)
                            il_rhs = translate_expr(rhs)
                case _:
                    il_op = op
                    il_lhs = translate_expr(lhs)
                    il_rhs = translate_expr(rhs)

            return MCILApply(
                sort=synthesize_sort(xmv_expr=xmv_expr),
                identifier=MCILIdentifier(symbol=il_op, indices=[]),
                children=[il_lhs, il_rhs]
            )
        case XMVUnop(op=op, arg=arg):
            match op:
                case "!":
                    il_op = "not"
                case _:
                    il_op = op

            return MCILApply(
                sort=synthesize_sort(xmv_expr=xmv_expr),
                identifier=MCILIdentifier(symbol=il_op, indices=[]),
                children=[translate_expr(arg)]
            )
        case _:
            raise ValueError(f"[translate_expr] unhandled expression {xmv_expr}, {xmv_expr.__class__}")

    raise ValueError(f"[translate_expr] {xmv_expr}")

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

# def synthesize_sort(xmv_expr: XMVExpr) -> MCILSort:
#     match xmv_expr:
#         case XMVIntegerConstant():
#             return MCIL_INT_SORT
#         case XMVBooleanConstant():
#             return MCIL_BOOL_SORT
#         case XMVWordConstant():
#             return MCIL_BITVEC_SORT(xmv_expr.width)
#         case XMVRangeConstant():
#             raise ValueError("not dealing with ranges yet")
#         case XMVBinop(op="+") | XMVBinop(op="-") | XMVBinop(op="*") | XMVBinop(op="/"):
#             return MCIL_BITVEC_SORT(32)
#         case XMVBinop(op="&") | XMVBinop(op="|") | XMVBinop(op="xor") | XMVBinop(op="xnor"):
#             return MCIL_BOOL_SORT
#         case XMVUnop(op="!"):
#             return MCIL_BOOL_SORT
#         case XMVUnop(op="-"):
#             return MCIL_INT_SORT
#         case XMVBinop(op="=") | XMVBinop(op="!="):
#             return MCIL_BOOL_SORT
#         case XMVBinop(op="<") | XMVBinop(op=">") | XMVBinop(op="<=") | XMVBinop(op=">="):
#             return MCIL_BITVEC_SORT(1)
#         case _:
#             raise ValueError(f"[synthesize_sort] Uncovered case: {xmv_expr}")

def gather_input(xmv_module: XMVModule, context: XMVContext) -> list[MCILVar]:
    result: list[MCILVar] = []
    for module_element in xmv_module.elements:
        match module_element:
            case XMVVarDeclaration(modifier="IVAR"):
                for (var_name, xmv_var_type) in module_element.var_list:
                    match xmv_var_type:
                        case XMVModuleType():
                            pass
                        case _:
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

def gather_output(xmv_module: XMVModule, context: XMVContext) -> list[MCILVar]:
    return []

def gather_local(xmv_module: XMVModule, context: XMVContext) -> list[MCILVar]:
    result: list[MCILVar] = []
    for module_element in xmv_module.elements:
        match module_element:
            case XMVVarDeclaration(modifier="VAR") | XMVVarDeclaration(modifier="FROZENVAR"):
                for (var_name, xmv_var_type) in module_element.var_list:
                    mcil_var = MCILVar(
                        var_type=MCILVarType.LOCAL,
                        sort=translate_type(xmv_var_type),
                        symbol=var_name.ident,
                        prime=False
                    )

                    result.append(mcil_var)
            # Definitions are actually macros...need to just expand them all
            # case XMVDefineDeclaration():
            #     define_list = module_element.define_list
            #     for define in define_list:
            #         name = define.name
            #         rhs_expr = define.expr

            #         context.vars[name.ident] = rhs_expr.type

            #         var = MCILVar(
            #             var_type=MCILVarType.LOCAL,
            #             sort=translate_type(rhs_expr.type),
            #             symbol=name.ident,
            #             prime=False
            #         )

            #         result.append(var)
            case _:
               pass
    
    return result

def gather_init(xmv_module: XMVModule) -> MCILExpr:
    return MCILConstant(sort=MCIL_BOOL_SORT, value=True)

def gather_trans(xmv_module: XMVModule) -> MCILExpr:
    return MCILConstant(sort=MCIL_BOOL_SORT, value=True)

def gather_inv(xmv_module: XMVModule) -> MCILExpr:
    inv_list: list[MCILExpr] = []

    for module_element in xmv_module.elements:
        match module_element:
            case XMVInvarDeclaration():
                invar = module_element.formula
                inv_list.append(translate_expr(invar))
            case _:
                pass

    return conjoin_list(inv_list) if len(inv_list) > 0 else MCILConstant(MCIL_BOOL_SORT, True)

def gather_subsystems(xmv_module: XMVModule) -> dict[str, tuple[str, list[str]]]:
    return {}

def gather_enums(xmv_module: XMVModule) -> list[MCILCommand]:
    return []

def gather_consts(xmv_module: XMVModule) -> list[MCILCommand]:
    return []

def gather_queries(xmv_module: XMVModule) -> dict[str, list[str]]:
    return {}

def translate_module(xmv_module: XMVModule) -> list[MCILCommand]:
    print(f"[translate_module] translating module {xmv_module.name}")
    il_commands: list[MCILCommand] = []
    xmv_context = XMVContext()

    (type_correct, xmv_context) = type_check(xmv_module)
    if not type_correct:
        raise ValueError("Not type correct")

    input = gather_input(xmv_module, xmv_context)

    output = gather_output(xmv_module, xmv_context)

    local = gather_local(xmv_module, xmv_context)

    init = gather_init(xmv_module)

    trans = gather_trans(xmv_module)

    inv = gather_inv(xmv_module)

    subsystems = gather_subsystems(xmv_module)

    define_system: MCILDefineSystem = \
        MCILDefineSystem(
            symbol=xmv_module.name,
            input=input,
            output=output,
            local=local,
            init=init,
            trans=trans,
            inv=inv,
            subsystems=subsystems
        )
    
    query: dict[str, list[str]] = gather_queries(xmv_module)


    if len(query) == 0:
        check_system = []
    else:
        check_system: list[MCILCommand] = \
            [MCILCheckSystem(
                sys_symbol=xmv_module.name,
                input=input,
                output=output,
                local=local,
                assumption={},
                fairness={},
                reachable={},
                current={},
                query=query,
            )]

    # commands
    enums = gather_enums(xmv_module)
    consts = gather_consts(xmv_module)

    return enums + consts + [define_system] + check_system

    return il_commands


def translate(xmv_specification: XMVSpecification) -> MCILProgram:
    commands: list[MCILCommand] = []
    for xmv_module in xmv_specification.modules:
        il_commands = translate_module(xmv_module=xmv_module)
        commands += il_commands

    return MCILProgram(commands=commands)

def main():
    argparser = argparse.ArgumentParser(
                           prog='nuXmv/NuSMV to IL translation',
                           description='Parses a nuXmv/NuSMV (.smv) file and translates the resulting AST into IL'
   )
    
    argparser.add_argument('filename')

    args = argparser.parse_args()

    parse_tree: XMVSpecification = parse(args.filename)
    print(f"[main] parsed specification in {args.filename}")

    result: MCILProgram = translate(parse_tree)

    with open(f"{Path(args.filename).with_suffix('.mcil').name}", "w") as f:
        f.write(str(result))

    # print(f"[main] result: {result}")

    (_, _) = sort_check(result)
    # print(res)
    return result

if __name__ == '__main__':
    main()