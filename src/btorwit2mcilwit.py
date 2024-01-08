import pickle
import sys
from pathlib import Path

from .btor_witness import *
from .mcil_witness import *
from .btor import *
from .parse_btorwit import parse_witness


def collect_var_symbols(btor_program: list[BtorNode]) -> dict[int, str]:
    vars = {}
    cur = 0
    for node in [n for n in btor_program if isinstance(n, BtorVar)]:
        if node.symbol.find("::") == -1 and node.symbol.find(".cur") != -1:
            vars[cur] = node.symbol.removesuffix(".cur")
        cur += 1
    return vars


def translate(
    btor_program: list[BtorNode],
    btor_witness: BtorWitness,
    query_symbol: str,
) -> Optional[MCILTrace]:
    trail: list[MCILState] = []

    vars = collect_var_symbols(btor_program)

    for frame in btor_witness.frames[:-1]:
        il_assigns: list[MCILAssignment] = []

        btor_assigns = [
            a for a in frame.state_assigns + frame.input_assigns if a.id in vars
        ]

        for btor_assign in btor_assigns:
            if isinstance(btor_assign, BtorBitVecAssignment):
                il_assigns.append(MCILBitVecAssignment(
                        vars[btor_assign.id], 
                        btor_assign.value
                    )
                )
            elif isinstance(btor_assign, BtorArrayAssignment):
                il_assigns.append(MCILArrayAssignment(
                        vars[btor_assign.id], 
                        (btor_assign.index, btor_assign.element)
                    )
                )
            else:
                raise NotImplementedError

        trail.append(
            MCILState(frame.index, il_assigns)
        )

    return MCILTrace(
        f"{query_symbol}_trace", MCILTrail(f"{query_symbol}_trail", trail), None
    )


def main(
    witness_path: Path, 
    program_path: Path,
    output_path: Path
) -> int:
    if witness_path.is_dir():
        witness_paths = [p for p in witness_path.glob("*")]
    elif witness_path.is_file():
        witness_paths = [witness_path]
    else:
        sys.stderr.write(f"Error: BTOR2 witness path must be file or directory.\n")
        return 1

    query_responses: list[MCILQueryResponse] = []

    for witness in witness_paths:
        with open(witness, "r") as f:
            witness_content = f.read()

        # check for empty witness
        # this means the query was unsat
        if witness_content == "":
            query_responses.append(MCILQueryResponse(
                witness.suffixes[-2][1:],
                    MCILQueryResult.UNSAT,
                    None,
                    None,
                    None
            ))
            continue
        
        btor_witness = parse_witness(witness_content)
        if not btor_witness:
            sys.stderr.write(f"Error: parse error for BTOR2 witness file '{witness}'.\n")
            return 1

        with open(program_path, "rb") as f:
            btor_program = pickle.load(f)

        if btor_witness:
            query_symbol = witness.suffixes[-2][1:]

            mcil_trace = translate(btor_program, btor_witness, query_symbol)

            query_responses.append(MCILQueryResponse(
                    query_symbol,
                    MCILQueryResult.SAT,
                    None,
                    mcil_trace,
                    None
                )
            )

    check_sys_response = MCILCheckSystemResponse(query_responses)

    with open(str(output_path), "w") as f:
        f.write(str(check_sys_response))

    return 0
