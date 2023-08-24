import sys
import json
from argparse import ArgumentParser
from pathlib import Path

from translate import parse

argparser = ArgumentParser(description="Translates an input IL program to JSON format.")
argparser.add_argument("input", help="input IL file")
argparser.add_argument("--output", help="output file to dump JSON data")
argparser.add_argument("--pretty", action="store_true", help="enable pretty JSON")

args = argparser.parse_args()

input_filename = Path(args.input)
output_filename = Path(args.output) if args.output else Path(f"{input_filename.stem}.json")

if not input_filename.is_file():
    print(f"Error: `{input_filename}` is not a valid file.")
    sys.exit(1)

with open(input_filename,"r") as file:
    program = parse(file.read())

if not program:
    print("Failed parsing")
    sys.exit(1)

with open(output_filename, "w") as f:
    json.dump(program.to_json(), f, indent=4 if args.pretty else None)