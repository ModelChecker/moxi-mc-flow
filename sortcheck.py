from pathlib import Path
import argparse
import sys

from src.util import eprint
from src.mcil import *
from src.parse_mcil import parse_mcil

FILE_NAME = Path(__file__).name


def main(input_path: Path, echo: bool) -> int:
    if not input_path.is_file():
        eprint(f"[{FILE_NAME}] '{input_path}' is not a valid file.\n")
        return 1

    with open(input_path, "r") as file:
        program = parse_mcil(file.read())

    if not program:
        eprint(f"[{FILE_NAME}] failed parsing\n")
        return 1

    (well_sorted, _) = sort_check(program)

    if not well_sorted:
        eprint(f"[{FILE_NAME}] failed sort check\n")
        return 1

    print(f"'{input_path}' is well sorted\n")

    if echo:
        print(program)

    return 0

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("input", help="input program to translate, language is inferred from file extension")
    parser.add_argument("--echo", action="store_true", help="echo input program")
    args = parser.parse_args()

    input_path = Path(args.input)
    echo = True if args.echo else False

    returncode = main(input_path, echo)

    sys.exit(returncode)