import sys
import json
from argparse import ArgumentParser
from pathlib import Path

if __name__ == "__main__" and __package__ is None:
    from il import sort_check
    from parse import parse
else:
    from .il import sort_check
    from .parse import parse


def main(input_path: Path, output_path: Path, do_sort_check: bool, do_pretty: bool) -> int:
    if not input_path.is_file():
        sys.stderr.write(f"Error: `{input_path}` is not a valid file.\n")
        return 1

    with open(input_path,"r") as file:
        program = parse(file.read())

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


if __name__ == "__main__":
    argparser = ArgumentParser(description="Translates an input IL program to JSON format.")
    argparser.add_argument("input", help="input IL file")
    argparser.add_argument("--output", help="output file to dump JSON data")
    argparser.add_argument("--pretty", action="store_true", help="enable pretty JSON")
    argparser.add_argument("--sort-check", action="store_true", help="enable sort checking")

    args = argparser.parse_args()

    input_path = Path(args.input)
    output_path = Path(args.output) if args.output else Path(f"{input_path.stem}.json")

    returncode = main(input_path, output_path, args.sort_check, args.pretty)
    sys.exit(returncode)

