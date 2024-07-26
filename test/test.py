import pathlib
import json
import difflib
import shutil
import subprocess
import sys
import argparse

from typing import cast

FILE_NAME = pathlib.Path(__file__).name
FILE_DIR = pathlib.Path(__file__).parent


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


def run_test(script: str, options: list[str], test: dict, keep: bool) -> bool:
    """Runs and prints status of `test` where `test` looks something like:

    `{
        "input": "file.moxi",
        "expected_output": "file.expect",
        "options": ["opt", ...]
    }`
    """
    status, diff = True, ""

    command = ["python3", script, test["input"]] + options

    if "options" in test:
        command += test["options"]

    if "output" in test:
        command += ["--output", test["output"]]

    print(" ".join(command))

    proc = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)

    try:
        if "expected_stdout" in test:
            # Both stdout and stderr are captured in proc.stdout
            test_output = proc.stdout.decode().splitlines()
            expected_output = test["expected_stdout"].splitlines()

            status, diff = run_diff(
                expected_output, test_output, test["input"], test["expected_stdout"]
            )
        if "expected_returncode" in test:
            # Both stdout and stderr are captured in proc.stdout
            test_returncode = proc.returncode
            expected_returncode = test["expected_returncode"]
            
            if test_returncode != expected_returncode:
                status = False
                diff = f"Expected {expected_returncode}, got {test_returncode}"
        if "expected_output" in test:
            # `expected_output` is a list of pairs of files 
            # each pair of files should be the same
            # this test should also have `output` as a field as well
            expected = cast(list[tuple[str,str]], test["expected_output"])

            for expect,out in expected:
                with open(out, "r") as f:
                    test_output = f.read().splitlines(keepends=True)
                with open(expect, "r") as f:
                    expected_output = f.read().splitlines(keepends=True)

                status, diff = run_diff(
                    expected_output, test_output, test["input"], expect
                )

                if not keep:
                    output_path = pathlib.Path(out)
                    if output_path.is_file():
                        output_path.unlink()
                    elif output_path.is_dir():
                        shutil.rmtree(output_path)

            output_path = pathlib.Path(test["output"])
            if output_path.is_dir():
                shutil.rmtree(output_path)
    except FileNotFoundError:
        print_fail(f"{test['input']}: file does not exist")
        return False

    if status:
        print_pass(f"{test['input']}")
    else:
        print_fail(f"{test['input']}\n{diff}")

    return status


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("config", help="config file that defines the tests to run")
    parser.add_argument("--keep", action="store_true", help="keep intermediate files")
    args = parser.parse_args()

    with open(args.config, "r") as f:
        config = json.load(f)

    if "script" in config:
        script = config["script"]
    else:
        print("'script' attribute not in test config, exiting")
        sys.exit(1)

    if "options" in config:
        options = config["options"]
    else:
        options = []

    if "tests" not in config:
        print("'tests' attribute not in test config, exiting")
        sys.exit(1)

    if any([not run_test(script, options, test, args.keep) for test in config["tests"]]):
        sys.exit(1)
        
    sys.exit(0)
