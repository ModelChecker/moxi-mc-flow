import argparse
import subprocess
from os.path import commonpath
from os import walk
from pathlib import Path
import shutil
import time
from typing import Callable

class Color:
    HEADER = "\033[95m"
    OKBLUE = "\033[94m"
    OKCYAN = "\033[96m"
    OKGREEN = "\033[92m"
    WARNING = "\033[93m"
    FAIL = "\033[91m"
    ENDC = "\033[0m"
    BOLD = "\033[1m"
    UNDERLINE = "\033[4m"

FILE_NAME = Path(__file__).name
FILE_DIR = Path(__file__).parent

translate_path = FILE_DIR / ".." / "translate.py"
modelcheck_path = FILE_DIR / ".." / "modelcheck.py"
catbtor_path = FILE_DIR / ".." / "btor2tools" / "build" / "bin" / "catbtor"
sortcheck_path = FILE_DIR / ".." / "sortcheck.py"
results_path = FILE_DIR / "resultsdir"

timeout = 120

def print_test(msg: str) -> None:
    print(f"[{Color.HEADER}TEST{Color.ENDC}] {msg}")

def print_pass(msg: str, test_results_path: Path) -> None:
    print(f"[{Color.OKGREEN}PASS{Color.ENDC}] {msg}")
    # print(f"Results written to {test_results_path}")

def print_fail(msg: str, test_results_path: Path) -> None:
    print(f"[{Color.FAIL}FAIL{Color.ENDC}] {msg}")
    # print(f"Results written to {test_results_path}")

def get_common_path(pass_files: list[Path], fail_files: list[Path]) -> Path:
    # special case where only one test total:
    # the common_path must be the parent of the test
    if len(pass_files + fail_files) == 1:
        if len(pass_files) == 1:
            return pass_files[0].parent
        else:
            return fail_files[0].parent
    else:
        return Path(commonpath([str(f) for f in pass_files + fail_files]))


def cleandir(dir: Path, quiet: bool):
    """Remove and create fresh dir, print a warning if quiet is False"""
    if dir.is_file():
        if not quiet:
            print(f"Overwriting {dir}")
        dir.rmdir()
    elif dir.is_dir():
        if not quiet:
            print(f"Overwriting {dir}")
        shutil.rmtree(dir)

    dir.mkdir()


def run_test(
    command: list[str], 
    output_dir: Path,
    pass_file: Path,
    fail_file: Path,
    should_pass: bool
) -> bool:
    global results_path

    test_dir = results_path / output_dir
    test_dir.mkdir(parents=True)

    stdout_path = test_dir / "stdout"
    stderr_path = test_dir /  "stderr"
    stdout_path.touch()
    stderr_path.touch()

    print_test(str(output_dir))
    test_start = time.perf_counter()

    try:
        proc = subprocess.run(command, capture_output=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        print_fail(f"{output_dir}", test_dir)

        with open(str(stderr_path), "w") as f:
            f.write(f"timeout after {timeout}s")

        with open(str(fail_file), "a") as f:
            f.write(f"{output_dir} timeout\n")

        return False

    test_end = time.perf_counter()

    if proc.returncode and should_pass:
        print_fail(f"{output_dir}", test_dir)

        with open(str(stderr_path), "w") as f:
            f.write(proc.stderr.decode("utf-8"))

        with open(str(stdout_path), "w") as f:
            f.write(proc.stdout.decode("utf-8"))

        with open(str(fail_file), "a") as f:
            f.write(f"{output_dir} {stderr_path}\n")

        return False
    else:
        print_pass(f"{output_dir} ({test_end - test_start:.5f}s)", test_dir)

        with open(str(stderr_path), "w") as f:
            f.write(proc.stderr.decode("utf-8"))

        with open(str(stdout_path), "w") as f:
            f.write(proc.stdout.decode("utf-8"))

        with open(str(pass_file), "a") as f:
            f.write(f"{output_dir} {test_end - test_start}s\n")
        
        return True


def test_nuxmv2mcil(
    pass_files: list[Path], 
    fail_files: list[Path]
) -> bool:
    global translate_path

    pass_file = results_path / "pass.txt"
    fail_file = results_path / "fail.txt"

    pass_file.touch()
    fail_file.touch()
    
    common_path = get_common_path(pass_files, fail_files)

    nuxmv2mcil_command: Callable[[Path,Path],list[str]] = (
        lambda file, output_dir: 
            ["python3", str(translate_path), str(file), "mcil", "--validate",
            "--output", str(results_path / output_dir / file.with_suffix(".mcil").name)]
    )


    for file in pass_files:
        output_dir = file.relative_to(common_path).with_suffix("")
        run_test(nuxmv2mcil_command(file, output_dir), output_dir, pass_file, fail_file, True)

    for file in fail_files:
        output_dir = file.relative_to(common_path).with_suffix("")
        run_test(nuxmv2mcil_command(file, output_dir), output_dir, pass_file, fail_file, False)

    return True


def test_any2btor(
    pass_files: list[Path], 
    fail_files: list[Path]
) -> bool:
    global translate_path

    pass_file = results_path / "pass.txt"
    fail_file = results_path / "fail.txt"

    pass_file.touch()
    fail_file.touch()
    
    common_path = get_common_path(pass_files, fail_files)

    mcil2btor_command: Callable[[Path,Path],list[str]] = (
        lambda file, output_dir: 
            ["python3", str(translate_path), str(file), "btor2", "--validate",
            "--output", str(results_path / output_dir / file.with_suffix("").name)]
    )

    for file in pass_files:
        output_dir = file.relative_to(common_path)
        run_test(mcil2btor_command(file, output_dir), output_dir, pass_file, fail_file, True)

    for file in fail_files:
        output_dir = file.relative_to(common_path)
        run_test(mcil2btor_command(file, output_dir), output_dir, pass_file, fail_file, False)

    return True


def test_modelcheck(
    pass_files: list[Path], 
    fail_files: list[Path]
) -> bool:
    global modelcheck_path

    pass_file = results_path / "pass.txt"
    fail_file = results_path / "fail.txt"

    pass_file.touch()
    fail_file.touch()

    common_path = get_common_path(pass_files, fail_files)

    modelcheck_command: Callable[[Path,Path],list[str]] = (
        lambda file, output_dir: 
            ["python3", str(modelcheck_path), str(file), "btormc", 
            "--output", str(results_path /output_dir), "--copyback"]
    )

    for file in pass_files:
        output_dir = file.relative_to(common_path)
        run_test(modelcheck_command(file, output_dir), output_dir, pass_file, fail_file, True)

    for file in fail_files:
        output_dir = file.relative_to(common_path)
        run_test(modelcheck_command(file, output_dir), output_dir, pass_file, fail_file, False)

    return True


def test_sortcheck(
    pass_files: list[Path], 
    fail_files: list[Path], 
) -> bool:
    global sortcheck_path

    pass_file = results_path / "pass.txt"
    fail_file = results_path / "fail.txt"
    pass_file.touch()
    fail_file.touch()

    common_path = get_common_path(pass_files, fail_files)

    sortcheck_command: Callable[[Path],list[str]] = (
        lambda file: ["python3", str(sortcheck_path), str(file)]
    )

    for file in pass_files:
        output_dir = file.relative_to(common_path)
        run_test(sortcheck_command(file), output_dir, pass_file, fail_file, True)

    for file in fail_files:
        output_dir = file.relative_to(common_path)
        run_test(sortcheck_command(file), output_dir, pass_file, fail_file, False)

    return True


def main(
    pass_files_path: Path, 
    fail_files_path: Path, 
    test: str
) -> None:
    """Runs tests by using `shutil.copytree`, which will run the `copy_function` on each file in the argument file directory tree while outputting files in an identical tree structure to the argument."""
    global results_path
    cleandir(results_path, False)

    def collect_files(files_path: Path) -> list[Path]:
        files = []

        if files_path.is_file():
            with open(str(files_path), "r") as f:
                content = f.read()

            for file in content.splitlines():
                files.append(Path(file))
        elif files_path.is_dir():
            for (dirpath,_,filenames) in walk(str(files_path)):
                files += [Path(dirpath, f) for f in filenames]
        else:
            print(f"Error: {files_path} does not exist.")
            return []

        return files

    pass_files = collect_files(pass_files_path)
    fail_files = collect_files(fail_files_path)

    if test ==  "nuxmv2btor":
        test_any2btor(pass_files, fail_files)
    elif test == "nuxmv2mcil":
        test_nuxmv2mcil(pass_files, fail_files)
    elif test == "mcil2btor":
        test_any2btor(pass_files, fail_files)
    elif test == "sortcheck":
        test_sortcheck(pass_files, fail_files)
    elif test == "modelcheck":
        test_modelcheck(pass_files, fail_files)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    
    parser.add_argument(
        "passfiles", 
        help="directory of or file that lists input files that should pass"
    )
    parser.add_argument(
        "failfiles", 
        help="directory of or file that lists input files that should fail"
    )
    parser.add_argument(
        "test", 
        choices=["nuxmv2btor", "nuxmv2mcil", "mcil2btor", "sortcheck", "modelcheck"],
        help="test to run"
    )
    parser.add_argument("--translate", help="path to translate.py")
    parser.add_argument("--modelcheck", help="path to modelcheck.py")
    parser.add_argument("--sortcheck", help="path to sortcheck.py")
    parser.add_argument("--catbtor", help="path to catbtor")
    parser.add_argument(
        "--resultsdir", 
        help="directory to output test logs and copyback data"
    )
    parser.add_argument(
        "--timeout", 
        help="max seconds before timeout", 
        type=int, 
        default=120
    )
    
    args = parser.parse_args()

    if args.translate:
        translate_path = Path(args.translate)

    if args.modelcheck:
        modelcheck_path = Path(args.modelcheck)

    if args.sortcheck:
        sortcheck_path = Path(args.sortcheck)

    if args.catbtor:
        catbtor_path = Path(args.catbtor)

    if args.resultsdir:
        results_path = Path(args.resultsdir)

    timeout = int(args.timeout)

    main(
        Path(args.passfiles), 
        Path(args.failfiles), 
        args.test
    )

