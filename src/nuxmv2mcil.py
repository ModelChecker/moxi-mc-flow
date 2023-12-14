import argparse
from pathlib import Path
from typing import cast
import subprocess

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
            raise ValueError("enums unsupported")
            return MCIL_ENUM_SORT(s[0])
        case XMVArray(type=t):
            return MCIL_ARRAY_SORT(MCIL_INT_SORT, translate_type(t))
        case _:
            raise ValueError(f"Unidentified type: {xmv_type}")
        
def coerce_int_to_bv(expr: MCILExpr) -> MCILExpr:
    if isinstance(expr, MCILConstant) and is_int_sort(expr.sort):
        return MCILConstant(
            MCIL_BITVEC_SORT(len(bin(expr.value)[2:])), 
            expr.value
        )
    return expr

def translate_expr(xmv_expr: XMVExpr, context: XMVContext) -> MCILExpr:
    match xmv_expr:
        case XMVIdentifier(ident=ident):
            if ident in context.defs:
                return translate_expr(context.defs[ident], context)

            return MCILVar(
                var_type=MCILVarType.LOCAL,
                sort=MCIL_BOOL_SORT, # TODO
                symbol=ident,
                prime=False
            )
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
                        children=[translate_expr(e) for e in fargs]
                    )
        case XMVBinOp(op=op, lhs=lhs, rhs=rhs):
            match op:
                case '&':
                    il_op = "and"
                    il_lhs = translate_expr(lhs, context)
                    il_rhs = translate_expr(rhs, context)
                case '|':
                    il_op = "or"
                    il_lhs = translate_expr(lhs, context)
                    il_rhs = translate_expr(rhs, context)
                case '!':
                    il_op = "not"
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
                case "/":
                    expr_type = cast(XMVWord, xmv_expr.type)
                    il_op = "bvsdiv" if expr_type.signed else "bvudiv"
                    il_lhs = coerce_int_to_bv(translate_expr(lhs, context))
                    il_rhs = coerce_int_to_bv(translate_expr(rhs, context))
                case "=":
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
                    il_op = "not"
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
                identifier=MCILIdentifier(symbol="extract", indices=[low, high]),
                children=[translate_expr(word, context)]
            )
        case _:
            raise ValueError(f"[translate_expr] unhandled expression {xmv_expr}, {xmv_expr.__class__}")

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
            case _:
               pass
    
    return result

def gather_init(xmv_module: XMVModule, context: XMVContext) -> MCILExpr:
    init_list = [translate_expr(e.formula, context) for e in xmv_module.elements if isinstance(e, XMVInitDeclaration)]

    return conjoin_list(init_list) if len(init_list) > 0 else MCILConstant(MCIL_BOOL_SORT, True)

def gather_trans(xmv_module: XMVModule, context: XMVContext) -> MCILExpr:
    trans_list = [translate_expr(e.formula, context) for e in xmv_module.elements if isinstance(e, XMVTransDeclaration)]

    return disjoin_list(trans_list) if len(trans_list) > 0 else MCILConstant(MCIL_BOOL_SORT, True)

def gather_inv(xmv_module: XMVModule, context: XMVContext) -> MCILExpr:
    inv_list = [translate_expr(e.formula, context) for e in xmv_module.elements if isinstance(e, XMVInvarDeclaration)]

    return conjoin_list(inv_list) if len(inv_list) > 0 else MCILConstant(MCIL_BOOL_SORT, True)

def gather_subsystems(xmv_module: XMVModule) -> dict[str, tuple[str, list[str]]]:
    return {}

def gather_enums(xmv_module: XMVModule) -> list[MCILCommand]:
    return []

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
    print(f"[translate_module] translating module {xmv_module.name}")
    il_commands: list[MCILCommand] = []
    xmv_context = XMVContext()

    (type_correct, xmv_context) = type_check(xmv_module)
    if not type_correct:
        raise ValueError("Not type correct")

    input = gather_input(xmv_module, xmv_context)
    output = gather_output(xmv_module, xmv_context)
    local = gather_local(xmv_module, xmv_context)

    init = gather_init(xmv_module, xmv_context)
    trans = gather_trans(xmv_module, xmv_context)
    inv = gather_inv(xmv_module, xmv_context)

    subsystems = gather_subsystems(xmv_module)

    define_system= MCILDefineSystem(
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
        check_system = []
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
    spec_path = Path(args.filename)
    pp_spec_path = spec_path.with_suffix(".smv.pp")

    proc = subprocess.run([
        "python3", 
        str(Path(__file__).parent / "preprocess_nuxmv.py"),
        str(spec_path),
        str(pp_spec_path)
    ], capture_output=True)

    parse_tree: XMVSpecification = parse(str(pp_spec_path))
    print(f"[main] parsed specification in {pp_spec_path}")

    result: MCILProgram = translate(parse_tree)

    with open(f"{Path(spec_path).with_suffix('.mcil').name}", "w") as f:
        f.write(str(result))

    # print(f"[main] result: {result}")

    (_, _) = sort_check(result)
    # print(res)
    return result

if __name__ == '__main__':
    main()