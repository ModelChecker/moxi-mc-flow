"""
TODO: Do not differentiate between unsat and unknown -- how to do this?
"""
import argparse
from pathlib import Path
import subprocess
import sys
import os
import shutil

from src.util import eprint
from src.nuxmv2mcil import main as nuxmv2mcil
from src.mcil2btor import main as mcil2btor
from src.btorwit2mcilwit import main as btorwit2mcilwit

FILE_NAME = Path(__file__).name
FILE_DIR = Path(__file__).parent
WORK_DIR = FILE_DIR / "__workdir__"

DEFAULT_BTORMC = FILE_DIR / "boolector" / "build" / "bin" / "btormc"
DEFAULT_AVR = FILE_DIR / "avr"
DEFAULT_PONO = FILE_DIR / "pono"


def cleandir(dir: Path, quiet: bool):
    """Remove and create fresh dir, print a warning if quiet is False"""
    if dir.is_file():
        if not quiet:
            print(f"[{FILE_NAME}] Overwriting '{dir}'")
        os.remove(dir)
    elif dir.is_dir():
        if not quiet:
            print(f"[{FILE_NAME}] Overwriting '{dir}'")
        shutil.rmtree(dir)

    os.mkdir(dir)


def any2btor(src_path: Path, target_path: Path, pickle_path: Path) -> int:
    if not src_path.is_file():
        eprint(f"[{FILE_NAME}] Error: source is not a file ({src_path})\n")
        return 1

    retcode = 0
    if src_path.suffix == ".smv":
        mcil_path = WORK_DIR / src_path.with_suffix(".mcil").name
        retcode += nuxmv2mcil(src_path, mcil_path, False)
        retcode += mcil2btor(mcil_path, target_path, pickle_path)
    elif src_path.suffix == ".mcil" or src_path.suffix == ".json":
        retcode += mcil2btor(src_path, target_path, pickle_path)
    else:
        eprint(f"[{FILE_NAME}] Error: file type unsupported ({src_path.suffix})\n")
        return 1

    return retcode


def run_btormc(btormc_path: Path, btor_path: Path, btor_witness_dir_path: Path) -> int:
    print(f"[{FILE_NAME}] running btormc over `{btor_path}`")
    label = btor_path.suffixes[-2][1:]

    proc = subprocess.run([btormc_path, btor_path, "--trace-gen-full"], capture_output=True)

    if proc.returncode:
        eprint(proc.stderr.decode("utf-8"))
        eprint(f"[{FILE_NAME}] Error: model checker failure for query '{label}'\n")
        return proc.returncode

    btor_witness_bytes = proc.stdout

    btor_witness_path = btor_witness_dir_path / btor_path.with_suffix(f".cex").name
    with open(btor_witness_path, "wb") as f:
        f.write(btor_witness_bytes)

    print(f"[{FILE_NAME}] btormc witness created at `{btor_witness_path}`")

    return 0


def run_avr(avr_path: Path, btor_path: Path, btor_witness_dir_path: Path) -> int:
    print(f"[{FILE_NAME}] running avr over `{btor_path}`")
    label = btor_path.suffixes[-2][1:]

    os.chdir(avr_path)
    proc = subprocess.run(["python3", "avr_pr.py", btor_path, "--witness"], capture_output=True)

    if proc.returncode:
        eprint(proc.stderr.decode("utf-8"))
        eprint(f"[{FILE_NAME}] Error: avr failure for query '{label}'\n")
        return proc.returncode

    avr_witness_path = [c for c in avr_path.glob("cex.witness")]
    btor_witness_path = btor_witness_dir_path / btor_path.with_suffix(f".cex").name
    
    os.chdir("..")
    if len(avr_witness_path) > 0:
        avr_witness_path[0].rename(str(btor_witness_path))
    else:
        btor_witness_path.touch()

    print(f"[{FILE_NAME}] avr witness created at `{btor_witness_path}`")

    return 0


def run_pono(pono_path: Path, btor_path: Path, btor_witness_dir_path: Path) -> int:
    print(f"[{FILE_NAME}] running pono over `{btor_path}`")

    label = btor_path.suffixes[-2][1:]
    pono_btor_path = pono_path / "shared" / btor_path.name

    os.chdir(pono_path)
    shutil.copy(btor_path, pono_btor_path)

    proc = subprocess.run([
        "docker", "run", "-it", "-d", "--name", "ponodocker", "--rm", "-v", "./shared:/home/pono-artifact", "pono-artifact"
    ], capture_output=True)

    if proc.returncode != 0:
        eprint(f"[{FILE_NAME}] error running docker for pono. Is it built?")
        return proc.returncode

    proc = subprocess.run([
        "docker", "exec", "-it", "ponodocker", "./pono/build/pono", "--witness", btor_path.name
    ], capture_output=True)
    btor_witness_bytes = proc.stdout

    proc = subprocess.run(["docker", "stop", "ponodocker"], capture_output=True)

    os.chdir("..")

    btor_witness_path = btor_witness_dir_path / btor_path.with_suffix(f".cex").name
    with open(btor_witness_path, "wb") as f:
        f.write(btor_witness_bytes)

    print(f"[{FILE_NAME}] pono witness created at ___")

    return 0


def model_check(
    input_path: Path, 
    output_path: Path, 
    use_btormc: bool, 
    use_avr: bool, 
    use_pono: bool,
    copyback: bool
) -> int:
    # TODO: btorsim may be useful for getting full witnesses -- as is it actually
    # does not output valid witness output (header is missing), so we don't use it.
    # NOTE: for a model checker like avr, this might be necessary for full traces
    if not input_path.is_file():
        eprint(f"[{FILE_NAME}] Error: source is not a file ({input_path})\n")
        return 1

    cleandir(WORK_DIR, False)

    pickled_btor_path = WORK_DIR / input_path.with_suffix(".pickle").name
    mcil_witness_path = WORK_DIR / input_path.with_suffix(".cex").name
    
    retcode = any2btor(input_path, WORK_DIR, pickled_btor_path)
    if retcode:
        return retcode

    btormc_witness_path = Path()
    avr_witness_path = Path()
    pono_witness_path = Path()
    for check_system_path in [d for d in WORK_DIR.iterdir() if d.is_dir()]:
        if use_btormc:
            btormc_witness_path = check_system_path / "btormc"
            btormc_witness_path.mkdir()

        if use_avr:
            avr_witness_path = check_system_path / "avr"
            avr_witness_path.mkdir()

        if use_pono:
            pono_witness_path = check_system_path / "pono"
            pono_witness_path.mkdir()
        
        for btor_path in check_system_path.glob("*.btor"):
            if use_btormc:
                run_btormc(DEFAULT_BTORMC, btor_path, btormc_witness_path)
            if use_avr:
                run_avr(DEFAULT_AVR, btor_path, avr_witness_path)
            if use_pono:
                run_pono(DEFAULT_PONO, btor_path, pono_witness_path)

        retcode = btorwit2mcilwit(btormc_witness_path, pickled_btor_path, mcil_witness_path)

        if copyback:
            shutil.copytree(WORK_DIR, output_path)
            print(f"[{FILE_NAME}] wrote files to `{output_path}`")
        else:
            mcil_witness_path.replace(output_path)
            print(f"[{FILE_NAME}] wrote MCIL witness to `{output_path}`")

        cleandir(WORK_DIR, True)

        if retcode:
            return retcode

    return 0


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("input", 
        help="input program to model check via translation to btor2")
    parser.add_argument("--output",  
        help="location of output check-system response")
    parser.add_argument("--copyback",  action="store_true",
        help="copy all intermediate translations and results to output location")
    parser.add_argument("--btormc", action="store_true", 
        help="enable btormc")
    parser.add_argument("--avr", action="store_true", 
        help="enable avr")
    parser.add_argument("--pono", action="store_true", 
        help="enable pono")
    args = parser.parse_args()

    input_path = Path(args.input)

    if not args.btormc and not args.avr and not args.pono:
        sys.exit(0)

    output_path = input_path.with_suffix(".cex")
    if args.output:
        output_path = Path(args.output)

    retcode = model_check(input_path, output_path, args.btormc, args.avr, args.pono, args.copyback)

    sys.exit(retcode)