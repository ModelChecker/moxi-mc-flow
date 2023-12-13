import argparse
import os
import sys
import subprocess
import shutil

from pathlib import Path

FILE_DIR = Path(__file__).parent
WORK_DIR = FILE_DIR / "__workdir__"

DEFAULT_MC = FILE_DIR / ".." / "boolector" / "build" / "bin" / "btormc" 
DEFAULT_SIM = FILE_DIR / ".." / "btor2tools" / "build" / "bin" / "btorsim"

IL2BTOR = FILE_DIR / "mcil2btor" / "mcil2btor.py"
BTORWIT2ILWIT = FILE_DIR / "mcil2btor" / "btorwit2mcilwit.py"


def cleandir(dir: Path, quiet: bool):
    """Remove and create fresh dir, print a warning if quiet is False"""
    if dir.is_file():
        if not quiet:
            print(f"WARNING: Overwriting '{dir}'")
        os.remove(dir)
    elif dir.is_dir():
        if not quiet:
            print(f"WARNING: Overwriting '{dir}'")
        shutil.rmtree(dir)

    os.mkdir(dir)


def main(src_path: Path, mc_path: Path, btorsim_path: Path) -> int:
    # TODO: btorsim may be useful for getting full witnesses -- as is it actually
    # does not output valid witness output (header is missing), so we don't use it.
    # NOTE: for a model checker like avr, this might be necessary for full traces

    if not src_path.is_file():
        sys.stderr.write(f"Error: given source is not a file ({src_path})\n")
        return 1

    if not mc_path.is_file():
        sys.stderr.write(f"Error: given model checker is not a file ({mc_path})\n")
        return 1

    # if not btorsim_path.is_file():
    #     sys.stderr.write(f"Error: given btorsim is not a file ({btorsim_path})\n")
    #     return 1

    if not WORK_DIR.is_dir():
        os.mkdir(WORK_DIR)

    pickled_btor_path = WORK_DIR / src_path.with_suffix(".pickle").name

    proc = subprocess.run(["python3", IL2BTOR, src_path, "--output", WORK_DIR, "--pickled-btor", pickled_btor_path])

    if proc.returncode:
        sys.stderr.write(f"Error: il2btor failure\n")
        return proc.returncode

    for check_system_path in [d for d in WORK_DIR.iterdir() if d.is_dir()]:
        btor_witness_dir_path = check_system_path / "wit"
        btor_witness_dir_path.mkdir()

        for btor_path in [l for l in check_system_path.iterdir() if l.suffix == ".btor"]:
            label = btor_path.suffixes[-2][1:]

            proc = subprocess.run([mc_path, btor_path, "--trace-gen-full"], capture_output=True)

            if proc.returncode:
                sys.stderr.write(proc.stderr.decode("utf-8"))
                sys.stderr.write(f"Error: model checker failure for query '{label}'\n")
                return proc.returncode

            btor_witness_bytes = proc.stdout

            btor_witness_path = btor_witness_dir_path / btor_path.with_suffix(f".cex").name
            with open(btor_witness_path, "wb") as f:
                f.write(btor_witness_bytes)

            # use btorsim to obtain full trace
            # proc = subprocess.run([
            #     btorsim_path, btor_path, btor_witness_path, "--states"
            # ], capture_output=True)

            # if proc.returncode:
            #     sys.stderr.write(proc.stderr.decode("utf-8"))
            #     sys.stderr.write(f"Error: btorsim failure for query '{label}'\n")
            #     return proc.returncode

            # btor_witness_bytes = proc.stdout

            # btor_witness_path = btor_path.with_suffix(f".cex") 
            # with open(btor_witness_path, "wb") as f:
            #     f.write(btor_witness_bytes)

        proc = subprocess.run(["python3", BTORWIT2ILWIT, btor_witness_dir_path, pickled_btor_path], capture_output=True)

        if proc.returncode:
            sys.stderr.write(proc.stderr.decode("utf-8"))
            sys.stderr.write(f"Error: btorwit2ilwit error\n")
            return proc.returncode

        print(proc.stdout.decode("utf-8"))

    return 0


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("source", help="IL program to model check")
    parser.add_argument("--modelchecker", default=str(DEFAULT_MC),
                            help="path to model checker executable (e.g., btormc)")
    parser.add_argument("--btorsim", default=str(DEFAULT_SIM),
                            help="path to btorsim executable")
    args = parser.parse_args()

    cleandir(WORK_DIR, False)

    src_path = Path(args.source)
    mc_path = Path(args.modelchecker)
    btorsim_path = Path(args.btorsim)

    returncode = main(src_path, mc_path, btorsim_path)
    sys.exit(returncode)

