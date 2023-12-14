import argparse
from pathlib import Path
import subprocess
import sys
import os
import shutil

from src.nuxmv2mcil import main as nuxmv2mcil
from src.mcil2btor import main as mcil2btor
from src.btorwit2mcilwit import main as btorwit2mcilwit

FILE_DIR = Path(__file__).parent
WORK_DIR = FILE_DIR / "__workdir__"

DEFAULT_BTORMC = FILE_DIR / "boolector" / "build" / "bin" / "btormc"
DEFAULT_AVR = FILE_DIR / "avr"


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


def any2btor(src_path: Path, target_path: Path, pickle_path: Path) -> int:
    if not src_path.is_file():
        sys.stderr.write(f"Error: source is not a file ({src_path})\n")
        return 1

    retcode = 0
    if src_path.suffix == ".smv":
        mcil_path = WORK_DIR / src_path.with_suffix(".mcil").name
        retcode += nuxmv2mcil(src_path, mcil_path, False)
        retcode += mcil2btor(mcil_path, target_path, pickle_path)
    elif src_path.suffix == ".mcil" or src_path.suffix == ".json":
        retcode += mcil2btor(src_path, target_path, pickle_path)
    else:
        sys.stderr.write(f"Error: file type unsupported ({src_path.suffix})\n")
        return 1

    return retcode


def run_btormc(btormc_path: Path, btor_path: Path, btor_witness_dir_path: Path) -> int:
    label = btor_path.suffixes[-2][1:]

    proc = subprocess.run([btormc_path, btor_path, "--trace-gen-full"], capture_output=True)

    if proc.returncode:
        sys.stderr.write(proc.stderr.decode("utf-8"))
        sys.stderr.write(f"Error: model checker failure for query '{label}'\n")
        return proc.returncode

    btor_witness_bytes = proc.stdout

    btor_witness_path = btor_witness_dir_path / btor_path.with_suffix(f".cex").name
    with open(btor_witness_path, "wb") as f:
        f.write(btor_witness_bytes)

    return 0


def model_check(src_path: Path, btorsim_path: Path) -> int:
    # TODO: btorsim may be useful for getting full witnesses -- as is it actually
    # does not output valid witness output (header is missing), so we don't use it.
    # NOTE: for a model checker like avr, this might be necessary for full traces

    if not src_path.is_file():
        sys.stderr.write(f"Error: given source is not a file ({src_path})\n")
        return 1

    # if not mc_path.is_file():
    #     sys.stderr.write(f"Error: given model checker is not a file ({mc_path})\n")
    #     return 1

    # if not btorsim_path.is_file():
    #     sys.stderr.write(f"Error: given btorsim is not a file ({btorsim_path})\n")
    #     return 1

    cleandir(WORK_DIR, False)

    btor2_path = WORK_DIR
    pickled_btor_path = WORK_DIR / src_path.with_suffix(".pickle").name
    retcode = any2btor(src_path, btor2_path, pickled_btor_path)

    if retcode:
        return retcode

    for check_system_path in [d for d in WORK_DIR.iterdir() if d.is_dir()]:
        btor_witness_dir_path = check_system_path / "wit"
        btor_witness_dir_path.mkdir()

        for btor_path in [l for l in check_system_path.iterdir() if l.suffix == ".btor"]:
            label = btor_path.suffixes[-2][1:]

            # ------------------------------------
            # btormc
            # ------------------------------------
            proc = subprocess.run([DEFAULT_BTORMC, btor_path, "--trace-gen-full"], capture_output=True)

            if proc.returncode:
                sys.stderr.write(proc.stderr.decode("utf-8"))
                sys.stderr.write(f"Error: btormc failure for query '{label}'\n")
                return proc.returncode

            btor_witness_bytes = proc.stdout

            btor_witness_path = btor_witness_dir_path / btor_path.with_suffix(f".btormc.cex").name
            with open(btor_witness_path, "wb") as f:
                f.write(btor_witness_bytes)

            # ------------------------------------
            # avr
            # ------------------------------------
            os.chdir(DEFAULT_AVR)
            proc = subprocess.run(["python3", "avr_pr.py", btor_path], capture_output=True)
            os.chdir("..")

            if proc.returncode:
                sys.stderr.write(proc.stderr.decode("utf-8"))
                sys.stderr.write(f"Error: avr failure for query '{label}'\n")
                return proc.returncode

            btor_witness_bytes = proc.stdout

            btor_witness_path = btor_witness_dir_path / btor_path.with_suffix(f".avr.cex").name
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

        mcil_witness_path = WORK_DIR / src_path.with_suffix(".cex").name

        retcode = btorwit2mcilwit(btor_witness_dir_path, pickled_btor_path, mcil_witness_path)

        if retcode:
            return retcode

    return 0


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("source", help="source program to model check via translation to btor2")
    # parser.add_argument("--targetloc", help="target location; should be a directory if targetlang is 'btor2', a filename otherwise")
    parser.add_argument("--sortcheck", action="store_true",
                        help="enable sort checking of emitted MCIL")
    args = parser.parse_args()

    src_path = Path(args.source)

    retcode = model_check(src_path, Path(""))

    sys.exit(retcode)