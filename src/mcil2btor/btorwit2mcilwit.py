import argparse
import pickle
import sys
from pathlib import Path

from btor_witness import *
from mcil_witness import *
from btor import *
from parse import parse_witness


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
    btor_witness: BtorWitness
) -> Optional[MCILTrace]:
    trail: list[MCILState] = []

    vars = collect_var_symbols(btor_program)

    for frame in btor_witness.frames:
        il_assigns: list[MCILAssignment] = []

        btor_assigns = [
            a for a in frame.state_assigns + frame.input_assigns if a.id in vars
        ]

        for btor_assign in btor_assigns:
            if isinstance(btor_assign, BtorBitVecAssignment):
                il_assigns.append(
                    MCILBitVecAssignment(
                        vars[btor_assign.id], 
                        btor_assign.value
                    )
                )
            elif isinstance(btor_assign, BtorArrayAssignment):
                il_assigns.append(
                    MCILArrayAssignment(
                        vars[btor_assign.id], 
                        (btor_assign.index, btor_assign.element)
                    )
                )
            else:
                raise NotImplementedError

        trail.append(
            MCILState(frame.index, il_assigns)
        )

    return MCILTrace("t0", MCILTrail("t1", trail), None)


def main(
    witness_path: Path, 
    program_path: Path,
    output_path: Path
) -> int:
    with open(witness_path, "r") as f:
        witness_content = f.read()
    
    btor_witness = parse_witness(witness_content)
    if not btor_witness:
        return 1

    # print(witness_path)

    with open(program_path, "rb") as f:
        btor_program = pickle.load(f)

    if btor_witness:
        il_witness = translate(btor_program, btor_witness)

        query_response = MCILQueryResponse(
            witness_path.suffixes[-2][1:],
            MCILQueryResult.SAT,
            None,
            il_witness,
            None
        )

        check_sys_reponse = MCILCheckSystemResponse(
            [query_response]
        )

        print(check_sys_reponse)

    return 0

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("witness", help="source BTOR2 witness program to translate")
    parser.add_argument("program", help="pickled BTOR2 program")
    parser.add_argument("--output", help="path output IL witness file; defaults to witness filename stem")
    args = parser.parse_args()

    witness_path = Path(args.witness)
    program_path = Path(args.program)
    output_path = Path(args.output) if args.output else Path(f"{witness_path.stem}")

    returncode = main(witness_path, program_path, output_path)
    sys.exit(returncode)
