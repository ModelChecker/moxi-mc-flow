from argparse import ArgumentParser
from pathlib import Path
import sys
from il import *


def from_json_identifier(contents: dict | str) -> ILIdentifier:
    if isinstance(contents, dict):
        return ILIdentifier(contents["symbol"], contents["indices"])
    else: # isinstance(contents, str)
        return ILIdentifier(str(contents), [])


def from_json_sort(contents: dict) -> ILSort:
    params: list[ILSort] =  []
    if "parameters" in contents:
        params = [from_json_sort(param) for param in contents["parameters"]]

    identifier = from_json_identifier(contents["identifier"])

    if identifier.symbol == "Bool" and len(identifier.indices) == 0:
        return IL_BOOL_SORT

    return ILSort(identifier, params)


def from_json_sorted_var(contents: dict) -> ILVar:
    sort = from_json_sort(contents["sort"])
    return ILVar(ILVarType.NONE, sort, contents["symbol"], False)


def from_json_expr(contents: dict, enums: dict[str, str]) ->  ILExpr:
    args: list[ILExpr] = []
    if "args" in contents:
        args = [from_json_expr(a, enums) for a in contents["args"]]
    
    identifier = from_json_identifier(contents["identifier"])

    if len(args) != 0:
        return ILApply(IL_NO_SORT, identifier, args)
    
    if identifier.symbol == "True":
        return ILConstant(IL_BOOL_SORT, True)
    elif identifier.symbol == "False":
        return ILConstant(IL_BOOL_SORT, False)
    elif re.match(r"0|[1-9]\d*", identifier.symbol):
        return ILConstant(IL_INT_SORT, int(identifier.symbol))
    elif re.match(r"#x[A-F0-9]+", identifier.symbol):
        return ILConstant(IL_BITVEC_SORT(len(identifier.symbol[2:])*4), int(identifier.symbol[2:], base=16))
    elif re.match(r"#b[01]+", identifier.symbol):
        return ILConstant(IL_BITVEC_SORT(len(identifier.symbol[2:])), int(identifier.symbol[2:], base=2))
    elif identifier.symbol in enums:
        return ILConstant(IL_ENUM_SORT(enums[identifier.symbol]), identifier.symbol)
    # else is variable

    prime: bool = False
    symbol: str = identifier.symbol
    if symbol[len(symbol)-1] == "'":
        prime = True
        symbol = symbol[:-1]

    return ILVar(ILVarType.NONE, IL_NO_SORT, symbol, prime)


def from_json(contents: dict) -> Optional[ILProgram]:
    dirname = os.path.dirname(__file__)

    with open(f"{dirname}/../../json-schema/schema/il.json", "r") as f:
        il_schema = json.load(f)

    resolver = RefResolver(f"file://{dirname}/../../json-schema/schema/", {})

    try:
        validate(contents, il_schema, resolver=resolver)
    except exceptions.SchemaError as se:
        print("Error: json schema invalid", se)
        return None
    except exceptions.ValidationError as ve:
        print("Error: json failed validation against schema.", ve)
        return None
    
    program: list[ILCommand] = []
    enums: dict[str, str] = {} # maps enum values to their sort symbol

    for cmd in contents:
        if cmd["command"] == "declare-sort":
            new = ILDeclareSort(cmd["symbol"], int(cmd["arity"]))
            program.append(new)
        elif cmd["command"] == "define-sort":
            definition = from_json_sort(cmd["definition"])
            new = ILDefineSort(cmd["symbol"], cmd["parameters"], definition)
            program.append(new)
        elif cmd["command"] == "declare-enum-sort":
            values = []
            for value in cmd["values"]:
                values.append(value)
                enums[value] = cmd["symbol"]

            new = ILDeclareEnumSort(cmd["symbol"], values)
            program.append(new)
        elif cmd["command"] == "declare-const":
            sort = from_json_sort(cmd["sort"])

            new = ILDeclareConst(cmd["symbol"], sort)
            program.append(new)
        elif cmd["command"] == "declare-fun":
            pass # TODO
        elif cmd["command"] == "define-fun":
            inputs = [from_json_sorted_var(i) for i in cmd["inputs"]]
            output = from_json_sort(cmd["output"])
            body = from_json_expr(cmd["body"], enums)

            new = ILDefineFun(cmd["symbol"], inputs, output, body)
            program.append(new)
        elif cmd["command"] == "define-system":
            input, output, local = [], [], []
            init, trans, inv = ILConstant(IL_BOOL_SORT, True), ILConstant(IL_BOOL_SORT, True), ILConstant(IL_BOOL_SORT, True)
            subsys = {}

            if "input" in cmd:
                input =  [from_json_sorted_var(i) for i in cmd["input"]]
            if "output" in cmd:
                output =  [from_json_sorted_var(i) for i in cmd["output"]]
            if "local" in cmd:
                local =  [from_json_sorted_var(i) for i in cmd["local"]]

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
                
            new  = ILDefineSystem(cmd["symbol"],  input, output, local, init, trans, inv, subsys)
            program.append(new)
        elif cmd["command"] == "check-system":
            # TODO: queries
            input, output, local = [], [], []
            assumption, reachable, fairness, current, query, queries = {}, {}, {}, {}, {}, {}

            if "input" in cmd:
                input =  [from_json_sorted_var(i) for i in cmd["input"]]
            if "output" in cmd:
                output =  [from_json_sorted_var(i) for i in cmd["output"]]
            if "local" in cmd:
                local =  [from_json_sorted_var(i) for i in cmd["local"]]

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
                
            new  = ILCheckSystem(cmd["symbol"],  input, output, local, assumption, fairness, reachable, current, query)
            program.append(new)

    return ILProgram(program)


def main(input_filename: str, output_filename: str, do_sort_check: bool) -> int:
    input_path = Path(input_filename)
    output_path = Path(output_filename)

    if not input_path.is_file():
        print(f"Error: `{input_filename}` is not a valid file.")
        sys.exit(1)

    with open(input_path, "r") as file:
        contents = json.load(file)
        program = from_json(contents)

    if not program:
        print("Failed parsing")
        sys.exit(1)

    if do_sort_check:
        (well_sorted, _) = sort_check(program)
        if not well_sorted:
            print("Failed sort check")
            sys.exit(2)

    with open(output_path, "w") as f:
        f.write(str(program))

    return 0


if __name__ == "__main__":
    argparser = ArgumentParser(description="Translates an input JSON program to IL format.")
    argparser.add_argument("input", help="input JSON file")
    argparser.add_argument("--output", help="output file to dump IL program")
    argparser.add_argument("--sort-check", action="store_true", help="enable sort checking")

    args = argparser.parse_args()

    input_filename = Path(args.input)
    output_filename = Path(args.output) if args.output else Path(f"{input_filename.stem}.mcil")

    main(str(input_filename), str(output_filename), args.sort_check)

