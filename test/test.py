import argparse
import subprocess
from pathlib import Path
import shutil

FILE_NAME = Path(__file__).name
FILE_DIR = Path(__file__).parent

translate_path = FILE_DIR/ ".." / "translate.py"
modelcheck_path = FILE_DIR / ".." / "modelcheck.py"


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

    try:
        proc = subprocess.run([
            "python3", str(translate_path), str(src_path), "mcil",
            "--output", str(mcil_path)
        ], capture_output=True, timeout=10)
    except subprocess.TimeoutExpired:
        print(f"[FAIL] {src_path}")
        with open(str(stderr_path), "w") as f:
            f.write("timeout after 10s")
        return dst

    if proc.returncode:
        print(f"[FAIL] {src_path}")
        with open(str(stderr_path), "w") as f:
            f.write(proc.stderr.decode("utf-8"))
    else:
        print(f"[PASS] {src_path}")

    return dst


def test_mcil2btor(src: str, dst: str) -> str:
    global translate_path

    src_path = Path(src)
    dst_path = Path(dst)

    if src_path.suffix != ".btor" and src_path.suffix != ".btor2":
        return dst

    pass_dir = dst_path.parent / "pass"
    fail_dir = dst_path.parent / "fail"
    cleandir(pass_dir, True)
    cleandir(fail_dir, True)

    btor_path = pass_dir / dst_path.with_suffix(".btor").name
    stderr_path = fail_dir /  dst_path.with_suffix(".stderr").name

    proc = subprocess.run([
        "python3", str(translate_path), str(src_path), "btor2",
        "--output", str(btor_path)
    ], capture_output=True)

    if proc.returncode:
        print(f"[FAIL] {src_path}")
        with open(str(stderr_path), "w") as f:
            f.write(proc.stderr.decode("utf-8"))
    else:
        print(f"[PASS] {src_path}")

    return dst


def test_modelcheck(src: str, dst: str) -> str:
    global modelcheck_path

    src_path = Path(src)
    dst_path = Path(dst)

    pass_dir = dst_path.parent / "pass"
    fail_dir = dst_path.parent / "fail"
    cleandir(pass_dir, True)
    cleandir(fail_dir, True)

    cex_path = pass_dir / dst_path.with_suffix(".cex").name
    stderr_path = fail_dir / dst_path.with_suffix(".stderr").name

    proc = subprocess.run([
        "python3", str(modelcheck_path), str(src_path), "--btormc", "--output", cex_path
    ], capture_output=True)

    if proc.returncode:
        print(f"[FAIL] {src_path}")
        with open(str(stderr_path), "w") as f:
            f.write(proc.stderr.decode("utf-8"))
    else:
        print(f"[PASS] {src_path}")

    return dst


def main(
    smvdir: Path, 
    resultsdir: Path,
    nuxmv2mcil: bool,
    mcil2btor: bool,
    modelcheck: bool
) -> None:
    cleandir(resultsdir, False)

    if nuxmv2mcil:
        nuxmv2mcil_dir = resultsdir / "nuxmv2mcil"
        shutil.copytree(
            smvdir, nuxmv2mcil_dir, copy_function=test_nuxmv2mcil
        )
    if mcil2btor:
        mcil2btor_dir = resultsdir / "mcil2btor"
        shutil.copytree(
            smvdir, mcil2btor_dir, copy_function=test_mcil2btor
        )
    if modelcheck:
        modelcheck_dir = resultsdir / "modelcheck"
        shutil.copytree(
            smvdir, modelcheck_dir, copy_function=test_modelcheck
        )

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("smvdir", help="directory of input SMV files")
    parser.add_argument("--translate", help="path to translate.py")
    parser.add_argument("--resultsdir", default=str(FILE_DIR / "resultsdir"),
                        help="directory to output test logs and copyback data")
    parser.add_argument("--nuxmv2mcil", action="store_true",
                        help="enable nuxmv2mcil test")
    parser.add_argument("--mcil2btor", action="store_true",
                        help="enable mcil2btor test")
    parser.add_argument("--modelcheck", action="store_true",
                        help="enable modelcheck test")
    args = parser.parse_args()

    if args.translate:
        translate_path = Path(args.translate)

    main(Path(args.smvdir), Path(args.resultsdir), args.nuxmv2mcil, args.mcil2btor, args.modelcheck)

