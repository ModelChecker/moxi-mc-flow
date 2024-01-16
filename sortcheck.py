from pathlib import Path
import argparse
import sys

from src.util import logger
from src.mcil import *
from src.parse_mcil import parse

FILE_NAME = Path(__file__).name


def main(input_path: Path, echo: bool) -> int:
    if not input_path.is_file():
        logger.error(f"{input_path} is not a valid file.")
        return 1

    program = parse(input_path)

    if not program:
        logger.error(f"Failed parsing")
        return 1

    (well_sorted, _) = sort_check(program)

    if not well_sorted:
        logger.error(f"Failed sort check")
        return 1

    if echo:
        print(program)
    else:
        print(f"{input_path} is well sorted")

    return 0

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("input", help="MCIL program to sort check")
    parser.add_argument("--echo", action="store_true", help="echo input program")
    args = parser.parse_args()

    input_path = Path(args.input)
    echo = True if args.echo else False

    returncode = main(input_path, echo)

    sys.exit(returncode)