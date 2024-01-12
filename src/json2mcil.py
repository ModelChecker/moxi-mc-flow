import sys
import os
import re
import json

from pathlib import Path
from jsonschema import validate, exceptions, RefResolver

from .mcil import *

def from_json_identifier(contents: dict | str) -> MCILIdentifier:
    if isinstance(contents, dict):
        return MCILIdentifier(contents["symbol"], contents["indices"])
    else: # isinstance(contents, str)
        return MCILIdentifier(str(contents), [])


def from_json_sort(contents: dict) -> MCILSort:
    params: list[MCILSort] =  []
    if "parameters" in contents:
        params = [from_json_sort(param) for param in contents["parameters"]]

    identifier = from_json_identifier(contents["identifier"])

    if identifier.symbol == "Bool" and len(identifier.indices) == 0:
        return MCIL_BOOL_SORT

    return MCILSort(identifier, params)


def from_json_expr(contents: dict, enums: dict[str, str]) ->  MCILExpr:
    args: list[MCILExpr] = []
    if "args" in contents:
        args = [from_json_expr(a, enums) for a in contents["args"]]
    
    identifier = from_json_identifier(contents["identifier"])

    if len(args) != 0:
        return MCILApply(MCIL_NO_SORT, identifier, args)
    
    if identifier.symbol == "true":
        return MCILConstant(MCIL_BOOL_SORT, True)
    elif identifier.symbol == "false":
        return MCILConstant(MCIL_BOOL_SORT, False)
    elif re.match(r"0|[1-9]\d*", identifier.symbol):
        return MCILConstant(MCIL_INT_SORT, int(identifier.symbol))
    elif re.match(r"#x[A-F0-9]+", identifier.symbol):
        return MCILConstant(MCIL_BITVEC_SORT(len(identifier.symbol[2:])*4), int(identifier.symbol[2:], base=16))
    elif re.match(r"#b[01]+", identifier.symbol):
        return MCILConstant(MCIL_BITVEC_SORT(len(identifier.symbol[2:])), int(identifier.symbol[2:], base=2))
    elif identifier.symbol in enums:
        return MCILConstant(MCIL_ENUM_SORT(enums[identifier.symbol]), identifier.symbol)
    # else is variable

    prime: bool = False
    symbol: str = identifier.symbol
    if symbol[len(symbol)-1] == "'":
        prime = True
        symbol = symbol[:-1]

    return MCILVar(MCIL_NO_SORT, symbol, prime)


def from_json(contents: dict) -> Optional[MCILProgram]:
    dirname = os.path.dirname(__file__)

    with open(f"{dirname}/../json-schema/schema/il.json", "r") as f:
        il_schema = json.load(f)

    resolver = RefResolver(f"file://{dirname}/../json-schema/schema/", {})

    try:
        validate(contents, il_schema, resolver=resolver)
    except exceptions.SchemaError as se:
        sys.stderr.write(f"Error: json schema invalid {se}\n")
        return None
    except exceptions.ValidationError as ve:
        sys.stderr.write(f"Error: json failed validation against schema {ve}\n")
        return None
    
    program: list[MCILCommand] = []
    enums: dict[str, str] = {} # maps enum values to their sort symbol

    for cmd in contents:
        if cmd["command"] == "declare-sort":
            new = MCILDeclareSort(cmd["symbol"], int(cmd["arity"]))
            program.append(new)
        elif cmd["command"] == "define-sort":
            definition = from_json_sort(cmd["definition"])
            new = MCILDefineSort(cmd["symbol"], cmd["parameters"], definition)
            program.append(new)
        elif cmd["command"] == "declare-enum-sort":
            values = []
            for value in cmd["values"]:
                values.append(value)
                enums[value] = cmd["symbol"]

            new = MCILDeclareEnumSort(cmd["symbol"], values)
            program.append(new)
        elif cmd["command"] == "declare-const":
            sort = from_json_sort(cmd["sort"])

            new = MCILDeclareConst(cmd["symbol"], sort)
            program.append(new)
        elif cmd["command"] == "declare-fun":
            pass # TODO
        elif cmd["command"] == "define-fun":
            inputs = [(i["symbol"], from_json_sort(i["sort"])) for i in cmd["inputs"]]
            output = from_json_sort(cmd["output"])
            body = from_json_expr(cmd["body"], enums)

            new = MCILDefineFun(cmd["symbol"], inputs, output, body)
            program.append(new)
        elif cmd["command"] == "define-system":
            input, output, local = [], [], []
            init, trans, inv = MCILConstant(MCIL_BOOL_SORT, True), MCILConstant(MCIL_BOOL_SORT, True), MCILConstant(MCIL_BOOL_SORT, True)
            subsys = {}

            if "input" in cmd:
                input = [(i["symbol"], from_json_sort(i["sort"])) for i in cmd["input"]]
            if "output" in cmd:
                output = [(i["symbol"], from_json_sort(i["sort"])) for i in cmd["output"]]
            if "local" in cmd:
                local = [(i["symbol"], from_json_sort(i["sort"])) for i in cmd["local"]]

            if "init" in cmd:
                init = from_json_expr(cmd["init"], enums)
            if "trans" in cmd:
                trans = from_json_expr(cmd["trans"], enums)
            if "inv" in cmd:
                inv = from_json_expr(cmd["inv"], enums)

            if "subsys" in cmd:
                for subsystem in cmd["subsys"]:
                    target = subsystem["target"]
                    subsys[subsystem["symbol"]] = (target["symbol"], target["arguments"])
                
            new  = MCILDefineSystem(cmd["symbol"],  input, output, local, init, trans, inv, subsys)
            program.append(new)
        elif cmd["command"] == "check-system":
            # TODO: queries
            input, output, local, queries = [], [], [], []
            assumption, reachable, fairness, current, query = {}, {}, {}, {}, {}

            if "input" in cmd:
                input = [(i["symbol"], from_json_sort(i["sort"])) for i in cmd["input"]]
            if "output" in cmd:
                output = [(i["symbol"], from_json_sort(i["sort"])) for i in cmd["output"]]
            if "local" in cmd:
                local = [(i["symbol"], from_json_sort(i["sort"])) for i in cmd["local"]]

            if "assumption" in cmd:
                assumption = { entry["symbol"]: from_json_expr(entry["formula"], enums) for entry in cmd["assumption"] }
            if "reachable" in cmd:
                reachable = { entry["symbol"]: from_json_expr(entry["formula"], enums) for entry in cmd["reachable"] }
            if "fairness" in cmd:
                fairness = { entry["symbol"]: from_json_expr(entry["formula"], enums) for entry in cmd["fairness"] }
            if "current" in cmd:
                current = { entry["symbol"]: from_json_expr(entry["formula"], enums) for entry in cmd["current"] }

            if "query" in cmd:
                query = { entry["symbol"]: entry["formulas"] for entry in cmd["query"] }

            if "queries" in cmd:
                queries = [{ q["symbol"]: q["formulas"] for q in entry } for entry in cmd["queries"]]
                
            new  = MCILCheckSystem(cmd["symbol"],  input, output, local, assumption, fairness, reachable, current, query, queries)
            program.append(new)

    return MCILProgram(program)


def main(
    input_path: Path, 
    output_path: Path, 
    do_sort_check: bool, 
    do_qfbv: bool, 
    int_width: int
) -> int:
    if not input_path.is_file():
        sys.stderr.write(f"Error: `{input_path}` is not a valid file.\n")
        return 1

    with open(input_path, "r") as file:
        contents = json.load(file)
        program = from_json(contents)

    if not program:
        sys.stderr.write("Failed parsing\n")
        return 1

    if do_sort_check:
        (well_sorted, _) = sort_check(program)
        if not well_sorted:
            sys.stderr.write("Failed sort check\n")
            return 2

    if do_qfbv:
        to_qfbv(program, int_width)

    with open(output_path, "w") as f:
        f.write(str(program))

    return 0

