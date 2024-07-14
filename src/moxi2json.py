import json
import sys
from pathlib import Path

from src import moxi, parse_moxi


def main(
    input_path: Path, output_path: Path, do_pretty: bool
) -> int:
    if not input_path.is_file():
        sys.stderr.write(f"Error: `{input_path}` is not a valid file.\n")
        return 1

    program = parse_moxi.parse(input_path)

    if not program:
        sys.stderr.write("Failed parsing\n")
        return 1

    (well_sorted, context) = moxi.sort_check(program)
    if not well_sorted:
        sys.stderr.write("Failed sort check\n")
        return 2

    with open(output_path, "w") as f:
        json.dump(program.to_json(context), f, indent=4 if do_pretty else None)
        return 0
