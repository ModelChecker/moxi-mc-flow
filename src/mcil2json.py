import sys
import json
from pathlib import Path

from .mcil import sort_check
from .parse_mcil import parse_mcil

def main(input_path: Path, output_path: Path, do_sort_check: bool, do_pretty: bool) -> int:
    if not input_path.is_file():
        sys.stderr.write(f"Error: `{input_path}` is not a valid file.\n")
        return 1

    with open(input_path,"r") as file:
        program = parse_mcil(file.read())

    if not program:
        sys.stderr.write("Failed parsing\n")
        return 1

    if do_sort_check:
        (well_sorted, _) = sort_check(program)
        if not well_sorted:
            sys.stderr.write("Failed sort check\n")
            return 2

    with open(output_path, "w") as f:
        json.dump(program.to_json(), f, indent=4 if do_pretty else None)
        return 0

