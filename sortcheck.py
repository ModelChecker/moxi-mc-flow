from pathlib import Path
import argparse
import sys

from src import log
from src import moxi
from src import parse_moxi

FILE_NAME = Path(__file__).name

def main(input_path: Path, echo: bool) -> int:
    if not input_path.is_file():
        log.error(f"{input_path} is not a valid file.", FILE_NAME)
        return 1

    program = parse_moxi.parse(input_path)

    if not program:
        log.error("Failed parsing", FILE_NAME)
        return 1

    (well_sorted, _) = moxi.sort_check(program)

    if not well_sorted:
        log.error("Failed sort check", FILE_NAME)
        return 1

    if echo:
        print(program)
    else:
        print(f"{input_path} is well sorted")

    return 0

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("input", help="MoXI program to sort check")
    parser.add_argument("--echo", action="store_true", help="echo input program")
    args = parser.parse_args()

    input_path = Path(args.input)
    echo = True if args.echo else False

    returncode = main(input_path, echo)

    sys.exit(returncode)