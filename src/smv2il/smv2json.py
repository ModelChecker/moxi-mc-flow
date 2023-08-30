import sys
import argparse

from pathlib import Path

if __name__ == "__main__" and __package__ is None:
    from nuxmv_pyparser import parse
    from translate import translate_parse_tree  # type: ignore
    from to_json import ast_to_json_to_file
else:
    from .nuxmv_pyparser import parse
    from .translate import translate_parse_tree  # type: ignore
    from .to_json import ast_to_json_to_file


def main(input_path: Path, output_path: Path) -> int:
    if not input_path.is_file():
        sys.stderr.write(f"Error: `{input_path}` is not a valid file.")
        return 1

    with open(input_path, "r") as file:
        nuxmv_ast = parse(file.read())

    if not nuxmv_ast:
        sys.stderr.write("Failed parsing")
        return 1

    il_ast = translate_parse_tree(nuxmv_ast)
    ast_to_json_to_file(il_ast, output_path)

    return 0


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Translates input SMV program to a JSON representation.")
    parser.add_argument("input", help="SMV program to translate")
    parser.add_argument("--output", help="path of file to output JSON; defaults to input file with .json extension")
    args = parser.parse_args()

    input_path = Path(args.input)
    output_path = Path(args.output) if args.output else Path(f"{input_path.stem}.json")

    returncode = main(input_path, output_path)
    sys.exit(returncode)