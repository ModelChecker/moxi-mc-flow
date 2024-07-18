import json
import pathlib
import sys

from src import moxi, parse_moxi, log

FILE_NAME = pathlib.Path(__file__).name

def main(
    input_path: pathlib.Path, output_path: pathlib.Path, do_sort_check: bool, do_pretty: bool = True
) -> int:
    if not input_path.is_file():
        log.error(f"'{input_path}' is not a valid file.", FILE_NAME)
        return 1

    if output_path.exists():
        log.error(f"Output path '{output_path}' already exists.", FILE_NAME)
        return 1

    program = parse_moxi.parse(input_path)

    if not program:
        log.error("Failed parsing\n", FILE_NAME)
        return 1

    if do_sort_check:
        (well_sorted, _) = moxi.sort_check(program)
        if not well_sorted:
            log.error("Failed sort check\n", FILE_NAME)
            return 2

    with open(output_path, "w") as f:
        try:
            json.dump(program.to_json(), f, indent=4 if do_pretty else None)
            return 0
        except RecursionError:
            sys.setrecursionlimit(20_000)
            json.dump(program.to_json(), f, indent=4 if do_pretty else None)
            return 0

