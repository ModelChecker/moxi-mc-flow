import argparse
from glob import glob
import os
import sys
import subprocess

from pathlib import Path

from il2btor.parse import parse as parse_il
from il2btor.il2btor import translate as il2btor
from btorwit2ilwit.parse import parse as parse_btorwit

FILE_DIR = Path(__file__).parent
WORK_DIR = FILE_DIR / "__workdir"

def main(src_path: Path, mc_path: Path, btorsim_path: Path) -> int:
    if not src_path.is_file():
        sys.stderr.write(f"Error: given source is not a file ({src_path})\n")
        return 1

    if not mc_path.is_file():
        sys.stderr.write(f"Error: given model checker is not a file ({mc_path})\n")
        return 1

    if not btorsim_path.is_file():
        sys.stderr.write(f"Error: given btorsim is not a file ({btorsim_path})\n")
        return 1

    os.mkdir(WORK_DIR)

    with open(src_path, "r") as f:
        il_program = parse_il(f.read())

    if not il_program:
        sys.stderr.write(f"Error: parse error ({src_path})\n")
        return 1

    btor_programs = il2btor(il_program)

    if not btor_programs:
        sys.stderr.write(f"Error: il2btor failure\n")
        return returncode

    for label, btor_program in btor_programs.items():
        btor_path = WORK_DIR / (src_path.stem + "." + label)

        with open(btor_path, "w") as f:
            for node in btor_program:
                f.write(str(node) + "\n")

        proc = subprocess.run([mc_path, btor_path], capture_output=True)

        if proc.returncode:
            sys.stderr.write(str(proc.stderr))
            sys.stderr.write(str(proc.stdout))
            sys.stderr.write(f"Error: model checker failure for query '{label}'\n")
            return proc.returncode

        # TODO: what if unsat?
        btor_witness_bytes = proc.stdout
        btor_witness_str = proc.stdout.decode()

        btorwit_path = btor_path.with_suffix(f".{label}.cex") 
        with open(btorwit_path, "wb") as f:
            f.write(btor_witness_bytes)

        btor_witness = parse_btorwit(btor_witness_str)

        if not btor_witness:
            sys.stderr.write("Error: btor witness parse failure\n")
            return 1

        print(btor_witness)

    return 0


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("source", help="IL program to model check")
    parser.add_argument("modelchecker", help="path to model checker executable (e.x., btormc)")
    parser.add_argument("btorsim", help="path to btorsim executable")
    args = parser.parse_args()

    src_path = Path(args.source)
    mc_path = Path(args.modelchecker)
    btorsim_path = Path(args.btorsim)

    returncode = main(src_path, mc_path, btorsim_path)
    sys.exit(returncode)


