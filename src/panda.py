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
    """Returns a mapping of each LTL proposition in `formula` (ex: `i = 4`, `i + j < 5`) to a symbol that's used in the input to PANDA. This is necessary since PANDA only handles boolean variables."""
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
    """Removes all smv.LTLProposition nodes from `formula`."""
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
    """Replaces the SPEC at the end of the PANDA output from:
        `SPEC f & EG TRUE`
    to:
        `__PANDASPEC__ f`
    """
    new = content

    new = re.sub(r"SPEC", "JUSTICE TRUE\n\n__PANDASPEC__", new)
    new = re.sub(r"& EG TRUE", "", new)

    return new


def run_panda(props: set[str], formula_name: str) -> Optional[smv.ModuleDeclaration]:
    """Runs PANDA on the file at `FORMULA_PATH` to generate an SMV-encoded automata of that LTL formula, then processes, parses, and returns the SMV output."""
    command = [str(PANDA_PATH), "-n", str(FORMULA_PATH)]
    log.debug(2, " ".join(command), FILE_NAME)
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
    """For every LTLSPEC in `module`, runs PANDA on that spec and composes the output SMV module with `module`. The result is an SMV module with a `__PANDASPEC__` property that holds if the corresponding LTLSPEC in the original module holds. 
    
    We have to use a custom `__PANDASPEC__` property instead of a SPEC/CTLSPEC since we don't support SPEC/CTLSPEC generally. So, to keep that functionality separate/open-ended, we introduce __PANDASPEC__ as an INVARSPEC that also considers FAIRNESS/JUSTICE properties, since the __PANDASPEC__ will always be a property of the form AG !f.
    """
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

        for prop,name in props.items():
            module.elements.append(
                smv.InvarDeclaration(smv.BinOp("=", smv.Identifier(name), prop.expr))
            )

    # clean up temporary files
    if FORMULA_PATH.exists():
        FORMULA_PATH.unlink()
    if PANDA_OUTPUT_PATH.exists():
        PANDA_OUTPUT_PATH.unlink()
