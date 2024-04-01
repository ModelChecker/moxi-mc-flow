import pathlib
import subprocess
import re
from typing import Optional

from src import log, parse_smv, smv

FILE_NAME = pathlib.Path(__file__).name

PARENT_PATH = pathlib.Path(__file__).parent
PANDA_PATH = PARENT_PATH / "PANDA" / "PANDAcore" / "PANDA"
FORMULA_PATH = PARENT_PATH / "__tmp__"
PANDA_OUTPUT_PATH = PARENT_PATH / "__tmp__.smv"


def map_propositions(
    formula: smv.Expr, context: smv.Context
) -> dict[smv.LTLProposition, str]:
    prop = {}

    cnt = 0
    for expr in smv.postorder(formula, context, True):
        if not isinstance(expr, smv.LTLProposition):
            continue

        prop[expr] = f"p{cnt}"
        cnt += 1

    return prop


def modify_ltl_formula(
    formula: smv.Expr, context: smv.Context, props: dict[smv.LTLProposition, str]
) -> None:
    for expr in smv.postorder(formula, context, True):
        if isinstance(expr, smv.UnOp) and isinstance(expr.arg, smv.LTLProposition):
            expr.arg = smv.Identifier(props[expr.arg])
        elif isinstance(expr, smv.BinOp):
            if isinstance(expr.lhs, smv.LTLProposition):
                expr.lhs = smv.Identifier(props[expr.lhs])
            if isinstance(expr.rhs, smv.LTLProposition):
                expr.rhs = smv.Identifier(props[expr.rhs])
        # else don't care


def process_panda_output(content: str, props: set[str], formula_name: str) -> str:
    new = content

    new = re.sub(r"SPEC", "JUSTICE TRUE\n\n__PANDASPEC__", new)
    new = re.sub(r"& EG TRUE", "", new)

    param_list = ",".join([p for p in props])
    new = re.sub(r"main", f"{formula_name}({param_list})", new) 

    # remove declared propositions -- we changed these to parameters
    new = re.sub(r"VAR.*(?=VAR\s)", "", new, count=1, flags=re.DOTALL)

    return new


def run_panda(props: set[str], formula_name: str) -> Optional[smv.ModuleDeclaration]:
    command = [str(PANDA_PATH), "-n", str(FORMULA_PATH)]
    print(" ".join(command))
    proc = subprocess.run(command, capture_output=True)

    panda_output = proc.stdout.decode()

    processed_output = process_panda_output(panda_output, props, formula_name)

    with open(PANDA_OUTPUT_PATH, "w") as f:
        f.write(processed_output)

    result = parse_smv.parse(PANDA_OUTPUT_PATH, False)

    if not result:
        log.error("PANDA output invalid", FILE_NAME)
        return None

    return result.modules[0]


def handle_ltlspecs(
    module: smv.ModuleDeclaration, context: smv.Context
) -> None:
    """For every LTLSPEC in `module`, runs PANDA on that spec and composes the output SMV module with `module`. The result is an SMV module with checks """
    for ltlspec in [
        e for e in module.elements if isinstance(e, smv.LTLSpecDeclaration)
    ]:
        props = map_propositions(ltlspec.formula, context)
        modify_ltl_formula(ltlspec.formula, context, props)

        with open(str(FORMULA_PATH), "w") as f:
            f.write(repr(ltlspec.formula))

        ltl_module = run_panda(set(props.values()), ltlspec.name)
        if ltl_module:
            [module.elements.append(el) for el in ltl_module.elements]

        new_var_decl = smv.VarDeclaration([], "VAR")
        for name in props.values():
            new_var_decl.var_list.append((smv.Identifier(name), smv.Boolean()))

        module.elements.append(new_var_decl)

        for prop,name in props.items():
            print(name)
            module.elements.append(
                smv.InvarDeclaration(smv.BinOp("=", smv.Identifier(name), prop.expr))
            )

    # clean up temporary files
    if FORMULA_PATH.exists():
        FORMULA_PATH.unlink()
    if PANDA_OUTPUT_PATH.exists():
        PANDA_OUTPUT_PATH.unlink()
