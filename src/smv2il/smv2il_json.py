import sys
import argparse

from pathlib import Path

from nuxmv_pyparser import parse
from translate import translate_parse_tree  # type: ignore
from to_json import ast_to_json_to_file


def main(input_filename: str, output_filename: str) -> int:
    input_path = Path(input_filename)

    if not input_path.is_file():
        sys.stderr.write(f"Error: `{input_path}` is not a valid file.")
        return 1

    with open(input_path, "r") as file:
        nuxmv_ast = parse(file.read())

    if not nuxmv_ast:
        sys.stderr.write("Failed parsing")
        return 1

    il_ast = translate_parse_tree(nuxmv_ast)
    ast_to_json_to_file(il_ast, output_filename)

    return 0


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Translates input SMv program to a JSON representation.")
    parser.add_argument("input", help="SMV program to translate")
    parser.add_argument("output", help="path of file to output JSON")
    args = parser.parse_args()

    returncode = main(args.input, args.output)
    sys.exit(returncode)