import pathlib
import json
import difflib
import subprocess
import sys
import argparse


FILE_NAME = pathlib.Path(__file__).name
FILE_DIR = pathlib.Path(__file__).parent

translate_path = FILE_DIR / ".." / "translate.py"
modelcheck_path = FILE_DIR / ".." / "modelcheck.py"
catbtor_path = FILE_DIR / ".." / "btor2tools" / "build" / "bin" / "catbtor"
sortcheck_path = FILE_DIR / ".." / "sortcheck.py"
results_path = FILE_DIR / "resultsdir"


class Color:
    HEADER = "\033[95m"
    OKBLUE = "\033[94m"
    OKCYAN = "\033[96m"
    PASS = "\033[92m"
    WARNING = "\033[93m"
    FAIL = "\033[91m"
    ENDC = "\033[0m"
    BOLD = "\033[1m"
    UNDERLINE = "\033[4m"


def print_pass(msg: str):
    print(f"[{Color.PASS}PASS{Color.ENDC}] {msg}")


def print_fail(msg: str):
    print(f"[{Color.FAIL}FAIL{Color.ENDC}] {msg}")


def run_diff(
    expected_output: "list[str]", test_output: "list[str]", fromfile: str, tofile: str
) -> "tuple[bool, str]":
    """Returns a pair whose first element is True if the `expected_output` and `test_output` are the same and False otherwise, and whose second element is the diff between `expected_output` and `test_output`."""
    result = difflib.unified_diff(
        expected_output,
        test_output,
        fromfile=fromfile,
        tofile=tofile,
    )

    status = True
    diff = ""
    for line in result:
        if line[0] in {"-", "+", "?"}:
            status = False
        diff += line

    return (status, diff)


def run_test(test: dict) -> bool:
    """Runs and prints status of `test` where `test` looks like:

    `{
        "input": "file.c2po",
        "expected_output": "file.c2po.expect",
        "options": ["opt", ...]
    }`

    See `config.json`.
    """
    status, diff = True, ""

    command = []

    proc = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)

    try:
        if "expected_output" in test:
            # Both stdout and stderr are captured in proc.stdout
            test_output = proc.stdout.decode().splitlines(keepends=True)

            with open(test["expected_output"], "r") as f:
                expected_output = f.read().splitlines(keepends=True)

            status, diff = run_diff(
                expected_output, test_output, test["input"], test["expected_output"]
            )
        elif "expected_c2po" in test:
            # See serialize.py for default dump file names
            input_path = pathlib.Path(test["input"])
            c2po_output_path = input_path.with_suffix(".out.c2po")

            with open(str(c2po_output_path), "r") as f:
                test_output = f.read().splitlines(keepends=True)

            with open(test["expected_c2po"], "r") as f:
                expected_output = f.read().splitlines(keepends=True)

            status, diff = run_diff(
                expected_output, test_output, test["input"], test["expected_c2po"]
            )

            c2po_output_path.unlink()
    except FileNotFoundError:
        print_fail(f"{test['input']}: file does not exist")
        return False

    if status:
        print_pass(f"{test['input']}")
    else:
        print_fail(f"{test['input']}\nCommand: {' '.join(command)}\n{diff}")

    return status


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "config", help="config file that defines the tests to run"
    )
    parser.add_argument("--translate", help="path to translate.py")
    parser.add_argument("--modelcheck", help="path to modelcheck.py")
    parser.add_argument("--sortcheck", help="path to sortcheck.py")
    parser.add_argument("--catbtor", help="path to catbtor")
    parser.add_argument(
        "--resultsdir", help="directory to output test logs and copyback data"
    )
    parser.add_argument(
        "--timeout", help="max seconds before timeout", type=int, default=120
    )
    parser.add_argument("subset", nargs="?", default="",
                        help="name of subset to run")

    args = parser.parse_args()

    if args.translate:
        translate_path = pathlib.Path(args.translate)

    if args.modelcheck:
        modelcheck_path = pathlib.Path(args.modelcheck)

    if args.sortcheck:
        sortcheck_path = pathlib.Path(args.sortcheck)

    if args.catbtor:
        catbtor_path = pathlib.Path(args.catbtor)

    if args.resultsdir:
        results_path = pathlib.Path(args.resultsdir)

    timeout = int(args.timeout)

    # tests is an array of JSON objects
    with open(args.config, "r") as f:
        config = json.load(f)
        
    sys.exit(0)
