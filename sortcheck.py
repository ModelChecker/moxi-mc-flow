import pathlib
import argparse
import sys
import json

from src import log
from src import moxi
from src import parse_moxi
from src import json2moxi

FILE_NAME = pathlib.Path(__file__).name
FILE_DIR = pathlib.Path(__file__).parent

JSON_SCHEMA = FILE_DIR / "json-schema" / "schema"

def main(input_path: pathlib.Path, echo: bool) -> int:
    if not input_path.is_file():
        log.error(f"{input_path} is not a valid file.", FILE_NAME)
        return 1

    if input_path.suffix == ".moxi":
        program = parse_moxi.parse(input_path)
    elif input_path.suffix == ".json":
        with open(input_path, "r") as file:
            contents = json.load(file)
            program = json2moxi.from_json(JSON_SCHEMA, contents)
    else:
        log.error(f"File extension not recognized ({input_path.suffix})\n\tSupported file extensions: .moxi, .json", FILE_NAME)
        return 1

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
    parser.add_argument("--jsonschema", help="path to `json-schema` directory for JSON validation")
    args = parser.parse_args()

    input_path = pathlib.Path(args.input)
    echo = True if args.echo else False

    if args.jsonschema:
        JSON_SCHEMA = pathlib.Path(args.jsonschema)

    returncode = main(input_path, echo)

    sys.exit(returncode)