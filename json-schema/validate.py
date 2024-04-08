import os
import json
import sys

from argparse import ArgumentParser
from pathlib import Path

import warnings
warnings.filterwarnings("ignore", category=DeprecationWarning)

from jsonschema import validate, exceptions, RefResolver

DIR = Path(os.path.dirname(__file__))
with open(DIR / "schema/moxi.json", "r") as f:
    il_schema = json.load(f)
resolver = RefResolver(f"file://{DIR}/../json-schema/schema/", {})

argparser = ArgumentParser(description="Validates an input JSON program against IL JSON schema.")
argparser.add_argument("input", help="input JSON file")
args = argparser.parse_args()

input_path = Path(args.input)

if not input_path.is_file():
    sys.stderr.write(f"Error: `{input_path}` is not a valid file.\n")
    sys.exit(1)

with open(input_path, "r") as file:
    contents = json.load(file)

try:
    validate(contents, il_schema, resolver=resolver)
except exceptions.SchemaError as se:
    sys.stderr.write(f"Error: json schema invalid {se}\n")
    sys.exit(1)
except exceptions.ValidationError as ve:
    sys.stderr.write(f"Error: json failed validation against schema {ve}\n")
    sys.exit(1)

print(f"{input_path} is valid")