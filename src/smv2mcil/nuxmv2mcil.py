import argparse
import sys
import parse as Parser
from nuxmv import *

# add the parent directory to access mcil AST
sys.path.insert(0, '..')

from mcil2btor import mcil as IL

def translate_type(xmv_type: XMVType) -> IL.MCILSort:
    match xmv_type:
        case XMVBoolean():
            return IL.MCIL_BOOL_SORT
        case XMVInteger():
            return IL.MCIL_INT_SORT
        case XMVReal():
            raise ValueError("nuXmv `real` type not supported in the IL (yet?)")
        case XMVClock():
            raise ValueError("nuXmv `clock` type not supported in the IL (yet?)")
        case XMVWord(width=w):
            return IL.MCIL_BITVEC_SORT(w)
        case XMVEnumeration():
            raise ValueError("TODO!")
        case XMVRange():
            raise ValueError("not in mcil.py AST?")
        case XMVArray(type=t):
            return IL.MCIL_ARRAY_SORT(IL.MCIL_INT_SORT, translate_type(t))
        case _:
            raise ValueError(f"Unidentified type: {xmv_type}")
        
def coerce_int_to_BV(expr: IL.MCILExpr) -> IL.MCILExpr:
    match expr:
        case IL.MCILConstant(sort=IL.MCIL_INT_SORT, value=v):
            return IL.MCILConstant(sort=IL.MCIL_BITVEC_SORT(len(bin(v)[2:])), value=v)
        case _:
            return expr

def translate_expr(xmv_expr: XMVExpr) -> IL.MCILExpr:
    match xmv_expr:
        case XMVIdentifier(ident=i):
            return IL.MCILVar(
                var_type=IL.MCILVarType.LOCAL,
                sort=IL.MCIL_BOOL_SORT, # TODO
                symbol=i,
                prime=False
            )
        case XMVIntegerConstant(integer=i):
            return IL.MCILConstant(sort=IL.MCIL_INT_SORT, value=i)
        case XMVBooleanConstant(boolean=b):
            return IL.MCILConstant(sort=IL.MCIL_BOOL_SORT, value=b)
        case XMVWordConstant():
            return IL.MCILConstant(
                sort=IL.MCIL_BITVEC_SORT(xmv_expr.width), 
                value=int(xmv_expr.value)
            )            
        case XMVFuncall(function_name=fname, function_args=fargs):
            match fname:
                case "signed":
                    return translate_expr(fargs[0])
                case "unsigned":
                    return translate_expr(fargs[0])
                case "next":
                    match fargs[0]:
                        case XMVIdentifier(ident=i):
                            return IL.MCILVar(
                                var_type=IL.MCILVarType.LOCAL,
                                sort=IL.MCIL_BOOL_SORT, # TODO
                                symbol=fargs[0].ident,
                                prime=True
                            )
                        case _:
                            raise ValueError("complex next expressions unsupported")
                    
                case _:
                    return IL.MCILApply(
                        sort=IL.MCIL_NO_SORT,
                        identifier=IL.MCILIdentifier(symbol=fname, indices=[]),
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
                    il_lhs = coerce_int_to_BV(translate_expr(lhs))
                    il_rhs = coerce_int_to_BV(translate_expr(rhs))
                case "+":
                    il_op = "bvadd"
                    il_lhs = coerce_int_to_BV(translate_expr(lhs))
                    il_rhs = coerce_int_to_BV(translate_expr(rhs))
                case "=":
                    il_op = "="
                    try:
                        il_lhs_sort = synthesize_sort(lhs)
                        match il_lhs_sort:
                            case IL.MCIL_INT_SORT:
                                il_lhs = coerce_int_to_BV(translate_expr(lhs))
                                il_rhs = translate_expr(rhs)
                            case _:
                                il_lhs = translate_expr(lhs)
                                il_rhs = translate_expr(rhs)
                    except ValueError:
                        try:
                            il_rhs_sort = synthesize_sort(rhs)
                            match il_rhs_sort:
                                case IL.MCIL_INT_SORT:
                                    il_rhs = coerce_int_to_BV(translate_expr(rhs))
                                    il_lhs = translate_expr(lhs)
                                case _:
                                    il_lhs = translate_expr(lhs)
                                    il_rhs = translate_expr(rhs)
                        except ValueError:
                            il_lhs = translate_expr(lhs)
                            il_rhs = translate_expr(rhs)
                case _:
                    il_op = op
                    il_lhs = translate_expr(lhs)
                    il_rhs = translate_expr(rhs)

            return IL.MCILApply(
                sort=synthesize_sort(xmv_expr=xmv_expr),
                identifier=IL.MCILIdentifier(symbol=il_op, indices=[]),
                children=[il_lhs, il_rhs]
            )
        case XMVUnop(op=op, arg=arg):
            match op:
                case "!":
                    il_op = "not"
                case _:
                    il_op = op

            return IL.MCILApply(
                sort=synthesize_sort(xmv_expr=xmv_expr),
                identifier=IL.MCILIdentifier(symbol=il_op, indices=[]),
                children=[translate_expr(arg)]
            )
        case _:
            raise ValueError(f"[translate_expr] unhandled expression {xmv_expr}, {xmv_expr.__class__}")

    raise ValueError(f"[translate_expr] {xmv_expr}")

def conjoin_list(expr_list: list[IL.MCILExpr]) -> IL.MCILExpr:
    if len(expr_list) == 1:
        return expr_list[0]
    else:
        head, *tail = expr_list
        and_ident: IL.MCILIdentifier = IL.MCILIdentifier(symbol="and", indices=[])
        return IL.MCILApply(
            sort=IL.MCIL_BOOL_SORT,
            identifier=and_ident,
            children=[head, conjoin_list(tail)]
        )

def synthesize_sort(xmv_expr: XMVExpr) -> IL.MCILSort:
    match xmv_expr:
        case XMVIntegerConstant():
            return IL.MCIL_INT_SORT
        case XMVBooleanConstant():
            return IL.MCIL_BOOL_SORT
        case XMVWordConstant():
            return IL.MCIL_BITVEC_SORT(xmv_expr.width)
        case XMVRangeConstant():
            raise ValueError("not dealing with ranges yet")
        case XMVBinop(op="+") | XMVBinop(op="-") | XMVBinop(op="*") | XMVBinop(op="/"):
            return IL.MCIL_BITVEC_SORT(0)
        case XMVBinop(op="&") | XMVBinop(op="|") | XMVBinop(op="xor") | XMVBinop(op="xnor"):
            return IL.MCIL_BOOL_SORT
        case XMVUnop(op="!"):
            return IL.MCIL_BOOL_SORT
        case XMVUnop(op="-"):
            return IL.MCIL_INT_SORT
        case XMVBinop(op="=") | XMVBinop(op="!="):
            return IL.MCIL_BOOL_SORT
        case XMVBinop(op="<") | XMVBinop(op=">") | XMVBinop(op="<=") | XMVBinop(op=">="):
            return IL.MCIL_BITVEC_SORT(0)
        case _:
            raise ValueError(f"[synthesize_sort] Uncovered case: {xmv_expr}")

def gather_input(xmv_module: XMVModule) -> list[IL.MCILVar]:
    result: list[IL.MCILVar] = []
    for module_element in xmv_module.elements:
        match module_element:
            case XMVVarDeclaration(modifier="IVAR"):
                for (var_name, xmv_var_type) in module_element.var_list:

                    match xmv_var_type:
                        case XMVModuleType():
                            pass
                        case _:
                            mcil_var = IL.MCILVar(
                                var_type=IL.MCILVarType.INPUT,
                                sort=translate_type(xmv_var_type),
                                symbol=var_name,
                                prime=False
                            )

                            result.append(mcil_var)
                        
            case _:
                pass
    
    return result

def gather_output(xmv_module: XMVModule) -> list[IL.MCILVar]:
    return []

def gather_local(xmv_module: XMVModule) -> list[IL.MCILVar]:
    result: list[IL.MCILVar] = []
    for module_element in xmv_module.elements:
        match module_element:
            case XMVVarDeclaration(modifier="VAR") | XMVVarDeclaration(modifier="FROZENVAR"):
                for (var_name, xmv_var_type) in module_element.var_list:
                    mcil_var = IL.MCILVar(
                        var_type=IL.MCILVarType.LOCAL,
                        sort=translate_type(xmv_var_type),
                        symbol=var_name,
                        prime=False
                    )

                    result.append(mcil_var)
            case XMVDefineDeclaration():
                define_list = module_element.define_list
                for define in define_list:
                    name = define.name
                    rhs_expr = define.expr

                    var = IL.MCILVar(
                        var_type=IL.MCILVarType.LOCAL,
                        sort=synthesize_sort(rhs_expr),
                        symbol=name,
                        prime=False
                    )

                    result.append(var)
            case _:
               pass
    
    return result

def gather_init(xmv_module: XMVModule) -> IL.MCILExpr:
    return IL.MCILConstant(sort=IL.MCIL_BOOL_SORT, value=True)

def gather_trans(xmv_module: XMVModule) -> IL.MCILExpr:
    return IL.MCILConstant(sort=IL.MCIL_BOOL_SORT, value=True)

def gather_inv(xmv_module: XMVModule) -> IL.MCILExpr:
    inv_list: list[IL.MCILExpr] = []
    for module_element in xmv_module.elements:
        match module_element:
            case XMVDefineDeclaration():
                define_list = module_element.define_list
                define_il_expr_list: list[IL.MCILExpr] = []
                for define in define_list:
                    name = define.name
                    rhs_expr = define.expr
                    lhs_var = IL.MCILVar(
                        var_type=IL.MCILVarType.OUTPUT,
                        sort=synthesize_sort(rhs_expr),
                        symbol=name,
                        prime=False
                    )

                    rhs_mcil_expr = translate_expr(xmv_expr=rhs_expr)
                    mcil_expr = IL.MCILApply(
                        sort=IL.MCIL_BOOL_SORT,
                        identifier=IL.MCILIdentifier(symbol="=", indices=[]),
                        children=[lhs_var, rhs_mcil_expr]
                    )

                    define_il_expr_list.append(mcil_expr)
                define_il_expr = conjoin_list(define_il_expr_list)
                inv_list.append(define_il_expr)
            case _:
                pass

    return conjoin_list(inv_list)

def gather_subsystems(xmv_module: XMVModule) -> dict[str, tuple[str, list[str]]]:
    return {}

def gather_enums(xmv_module: XMVModule) -> list[IL.MCILCommand]:
    return []

def gather_consts(xmv_module: XMVModule) -> list[IL.MCILCommand]:
    return []

def gather_queries(xmv_module: XMVModule) -> dict[str, list[str]]:
    return {}

def translate_module(xmv_module: XMVModule) -> list[IL.MCILCommand]:
    print(f"[translate_module] translating module {xmv_module.name}")
    il_commands: list[IL.MCILCommand] = []

    input = gather_input(xmv_module)

    output = gather_output(xmv_module)

    local = gather_local(xmv_module)

    init = gather_init(xmv_module)

    trans = gather_trans(xmv_module)

    inv = gather_inv(xmv_module)

    subsystems = gather_subsystems(xmv_module)

    define_system: IL.MCILDefineSystem = \
        IL.MCILDefineSystem(
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
        check_system: list[IL.MCILCommand] = \
            [IL.MCILCheckSystem(
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


def translate(xmv_specification: XMVSpecification) -> IL.MCILProgram:
    commands: list[IL.MCILCommand] = []
    for xmv_module in xmv_specification.modules:
        il_commands = translate_module(xmv_module=xmv_module)
        commands += il_commands

    return IL.MCILProgram(commands=commands)

def main():
    argparser = argparse.ArgumentParser(
                           prog='nuXmv/NuSMV to IL translation',
                           description='Parses a nuXmv/NuSMV (.smv) file and translates the resulting AST into IL'
   )
    
    argparser.add_argument('filename')

    args = argparser.parse_args()

    parse_tree: XMVSpecification = Parser.parse(args.filename)
    print(f"[main] parsed specification in {args.filename}")

    result: IL.MCILProgram = translate(parse_tree)

    # print(f"[main] result: {result}")

    (_, _) = IL.sort_check(result)
    # print(res)
    return result

if __name__ == '__main__':
    main()