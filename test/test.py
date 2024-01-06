import argparse
import subprocess
from pathlib import Path
import shutil
import time

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

timeout = 120

def print_pass(msg: str) -> None:
    print(f"[{Color.OKGREEN}PASS{Color.ENDC}] {msg}")

def print_fail(msg: str) -> None:
    print(f"[{Color.FAIL}FAIL{Color.ENDC}] {msg}")


def cleandir(dir: Path, quiet: bool):
    """Remove and create fresh dir, print a warning if quiet is False"""
    if dir.is_file():
        if not quiet:
            print(f"Overwriting '{dir}'")
        dir.rmdir()
    elif dir.is_dir():
        if not quiet:
            print(f"Overwriting '{dir}'")
        shutil.rmtree(dir)

    dir.mkdir()


def test_nuxmv2mcil(src: str, dst: str) -> str:
    global translate_path

    src_path = Path(src)
    dst_path = Path(dst)

    if src_path.suffix != ".smv":
        return dst

    pass_dir = dst_path.parent / "pass"
    fail_dir = dst_path.parent / "fail"
    if not pass_dir.exists():
        pass_dir.mkdir()
    if not fail_dir.exists():
        fail_dir.mkdir()

    mcil_path = pass_dir / dst_path.with_suffix(".mcil").name
    stderr_path = fail_dir /  dst_path.with_suffix(".stderr").name

    print(f"[TEST] {src}")
    test_start = time.perf_counter()

    try:
        proc = subprocess.run([
            "python3", str(translate_path), str(src_path), "mcil",
            "--output", str(mcil_path), "--validate"
        ], capture_output=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        print_fail(f"{src_path}")
        with open(str(stderr_path), "w") as f:
            f.write(f"timeout after {timeout}s")
        return dst

    test_end = time.perf_counter()

    if proc.returncode:
        print_fail(f"{src_path}")
        with open(str(stderr_path), "w") as f:
            f.write(proc.stderr.decode("utf-8"))
    else:
        print_pass(f"{src_path} ({test_end - test_start}s)")

    return dst


def test_nuxmv2btor(src: str, dst: str) -> str:
    global translate_path

    src_path = Path(src)
    dst_path = Path(dst)

    if src_path.suffix != ".smv":
        return dst

    pass_dir = dst_path.parent / "pass"
    fail_dir = dst_path.parent / "fail"
    if not pass_dir.exists():
        pass_dir.mkdir()
    if not fail_dir.exists():
        fail_dir.mkdir()

    btor_path = pass_dir / dst_path.with_suffix(".btor").name
    stderr_path = fail_dir /  dst_path.with_suffix(".stderr").name

    print(f"[TEST] {src}")
    test_start = time.perf_counter()

    try:
        proc = subprocess.run([
            "python3", str(translate_path), str(src_path), "btor2",
            "--output", str(btor_path), "--validate"
        ], capture_output=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        print_fail(f"{src_path}")
        with open(str(stderr_path), "w") as f:
            f.write(f"timeout after {timeout}s")
        return dst

    test_end = time.perf_counter()

    if proc.returncode:
        print_fail(f"{src_path}")
        with open(str(stderr_path), "w") as f:
            f.write(proc.stderr.decode("utf-8"))
        return dst
    
    for btor_file in btor_path.rglob("*.btor"):
        proc = subprocess.run([
            str(catbtor_path), str(btor_file)
        ], capture_output=True)

        if proc.returncode:
            print_fail(f"{src_path}")
            with open(str(stderr_path), "w") as f:
                f.write(proc.stderr.decode("utf-8"))
            return dst

    print_pass(f"{src_path} ({test_end - test_start}s)")

    return dst


def test_mcil2btor(src: str, dst: str) -> str:
    global translate_path

    src_path = Path(src)
    dst_path = Path(dst)

    if src_path.suffix != ".mcil":
        return dst

    pass_dir = dst_path.parent / "pass"
    fail_dir = dst_path.parent / "fail"
    if not pass_dir.exists():
        pass_dir.mkdir()
    if not fail_dir.exists():
        fail_dir.mkdir()

    btor_path = pass_dir / dst_path.with_suffix(".btor").name
    stderr_path = fail_dir /  dst_path.with_suffix(".stderr").name

    print(f"[TEST] {src}")
    test_start = time.perf_counter()

    try:
        proc = subprocess.run([
            "python3", str(translate_path), str(src_path), "btor2",
            "--output", str(btor_path), "--validate"
        ], capture_output=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        print_fail(f"{src_path}")
        with open(str(stderr_path), "w") as f:
            f.write(f"timeout after {timeout}s")
        return dst

    test_end = time.perf_counter()

    if proc.returncode:
        print_fail(f"{src_path}")
        with open(str(stderr_path), "w") as f:
            f.write(proc.stderr.decode("utf-8"))
        return dst
    
    # for btor_file in btor_path.rglob("*.btor"):
    #     proc = subprocess.run([
    #         str(catbtor_path), str(btor_file)
    #     ], capture_output=True)

    #     if proc.returncode:
    #         print_fail(f"{src_path}")
    #         with open(str(stderr_path), "w") as f:
    #             f.write(proc.stderr.decode("utf-8"))
    #         return dst

    print_pass(f"{src_path} ({test_end - test_start}s)")

    return dst


def test_modelcheck(src: str, dst: str) -> str:
    global modelcheck_path

    print(f"[TEST] {src}")

    src_path = Path(src)
    dst_path = Path(dst)

    pass_dir = dst_path.parent / "pass"
    fail_dir = dst_path.parent / "fail"
    cleandir(pass_dir, True)
    cleandir(fail_dir, True)

    cex_path = pass_dir / dst_path.with_suffix(".cex").name
    stderr_path = fail_dir / dst_path.with_suffix(".stderr").name

    test_start = time.perf_counter()

    try:
        proc = subprocess.run([
            "python3", str(modelcheck_path), str(src_path), "--btormc", "--output", cex_path
        ], capture_output=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        print_fail(f"{src_path}")
        with open(str(stderr_path), "w") as f:
            f.write(f"timeout after {timeout}s")
        return dst

    test_end = time.perf_counter()

    if proc.returncode:
        print_fail(f"{src_path}")
        with open(str(stderr_path), "w") as f:
            f.write(proc.stderr.decode("utf-8"))
    else:
        print_pass(f"{src_path} ({test_end - test_start}s)")

    return dst


def test_sortcheck(src: str, dst: str) -> str:
    global sortcheck_path

    src_path = Path(src)
    dst_path = Path(dst)

    if src_path.suffix != ".mcil":
        return dst

    pass_dir = dst_path.parent / "pass"
    fail_dir = dst_path.parent / "fail"
    if not pass_dir.exists():
        pass_dir.mkdir()
    if not fail_dir.exists():
        fail_dir.mkdir()

    stdout_path = pass_dir / dst_path.with_suffix(".stdout").name
    stderr_path = fail_dir /  dst_path.with_suffix(".stderr").name

    # print(f"[TEST] {src}")
    test_start = time.perf_counter()

    try:
        proc = subprocess.run([
            "python3", str(sortcheck_path), str(src_path)
        ], capture_output=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        print_fail(f"{src_path}")
        with open(str(stderr_path), "w") as f:
            f.write(f"timeout after {timeout}s")
        return dst

    test_end = time.perf_counter()

    if proc.returncode:
        print_fail(f"{src_path}")
        with open(str(stderr_path), "w") as f:
            f.write(proc.stderr.decode("utf-8"))
    else:
        print_pass(f"{src_path} ({test_end - test_start}s)")
        with open(str(stdout_path), "w") as f:
            f.write(proc.stdout.decode("utf-8"))

    return dst


def main(
    dir: Path, 
    resultsdir: Path,
    nuxmv2mcil: bool,
    nuxmv2btor: bool,
    mcil2btor: bool,
    modelcheck: bool,
    sortcheck: bool
) -> None:
    """Runs tests by using `shutil.copytree`, which will run the `copy_function` on each file in the argument file directory tree while outputting files in an identical tree structure to the argument."""
    cleandir(resultsdir, False)

    if nuxmv2mcil:
        nuxmv2mcil_dir = resultsdir / "nuxmv2mcil"
        shutil.copytree(
            dir, nuxmv2mcil_dir, copy_function=test_nuxmv2mcil
        )
    if nuxmv2btor:
        nuxmv2btor_dir = resultsdir / "nuxmv2btor"
        shutil.copytree(
            dir, nuxmv2btor_dir, copy_function=test_nuxmv2btor
        )
    if mcil2btor:
        mcil2btor_dir = resultsdir / "mcil2btor"
        shutil.copytree(
            dir, mcil2btor_dir, copy_function=test_mcil2btor
        )
    if modelcheck:
        modelcheck_dir = resultsdir / "modelcheck"
        shutil.copytree(
            dir, modelcheck_dir, copy_function=test_modelcheck
        )
    if sortcheck:
        modelcheck_dir = resultsdir / "sortcheck"
        shutil.copytree(
            dir, modelcheck_dir, copy_function=test_sortcheck
        )

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("dir", help="directory of input files")
    parser.add_argument("--translate", help="path to translate.py")
    parser.add_argument("--modelcheck-script", help="path to modelcheck.py")
    parser.add_argument("--catbtor", help="path to catbtor")
    parser.add_argument("--resultsdir", default=str(FILE_DIR / "resultsdir"),
                        help="directory to output test logs and copyback data")
    parser.add_argument("--nuxmv2mcil", action="store_true",
                        help="enable nuxmv2mcil test")
    parser.add_argument("--nuxmv2btor", action="store_true",
                        help="enable nuxmv2btor test")
    parser.add_argument("--mcil2btor", action="store_true",
                        help="enable mcil2btor test")
    parser.add_argument("--modelcheck", action="store_true",
                        help="enable modelcheck test")
    parser.add_argument("--sortcheck", action="store_true",
                        help="enable sortcheck test")
    parser.add_argument("--timeout", help="max seconds before timeout", 
                        type=int, default=120)
    args = parser.parse_args()

    if args.translate:
        translate_path = Path(args.translate)

    if args.modelcheck_script:
        modelcheck_path = Path(args.modelcheck_script)

    if args.catbtor:
        catbtor_path = Path(args.catbtor)

    timeout = int(args.timeout)

    main(
        Path(args.dir), 
        Path(args.resultsdir), 
        args.nuxmv2mcil, 
        args.nuxmv2btor, 
        args.mcil2btor, 
        args.modelcheck,
        args.sortcheck
    )

