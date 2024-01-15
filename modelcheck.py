import argparse
import logging
from pathlib import Path
import subprocess
import sys
import os
import shutil
import time
from typing import Optional

from src.util import cleandir, rmdir, logger
from src.btorwit2mcilwit import main as btorwit2mcilwit
from src.mcilwit2nuxmvwit import main as mcilwit2nuxmvwit

FILE_NAME = Path(__file__).name
FILE_DIR = Path(__file__).parent
WORK_DIR = FILE_DIR / "__workdir__"

DEFAULT_BTORMC = FILE_DIR / "boolector" / "build" / "bin" / "btormc"
DEFAULT_AVR = FILE_DIR / "avr"
DEFAULT_TRANSLATE = FILE_DIR / "translate.py"


def run_btormc(btormc_path: Path, btor_path: Path, kmax: int, kind: bool) -> int:
    logger.info(f"running btormc over {btor_path}")
    label = btor_path.stem

    command = [str(btormc_path), str(btor_path), "-kmax", str(kmax), "--trace-gen-full"]
    
    if kind:
        command.append("--kind")

    start_mc = time.perf_counter()
    
    proc = subprocess.run(command, capture_output=True)
    
    end_mc = time.perf_counter()

    if proc.returncode:
        logger.error(proc.stderr.decode("utf-8"))
        logger.error(f"Error: btormc failure for query '{label}'")
        return proc.returncode

    logger.info(f"done model checking in {end_mc-start_mc}s")

    btor_witness_bytes = proc.stdout

    btor_witness_path = btor_path.with_suffix(f".btor2.cex")
    with open(btor_witness_path, "wb") as f:
        f.write(btor_witness_bytes)

    logger.info(f"btormc witness created at {btor_witness_path}")

    return 0


def run_avr(avr_path: Path, btor_path: Path, kmax: int, kind: bool) -> int:
    absolute_btor_path = btor_path.absolute()

    logger.info(f"running avr over {absolute_btor_path}")
    label = absolute_btor_path.stem

    avr_output_path = absolute_btor_path.parent
    avr_results_path = avr_output_path / "work_test"

    os.chdir(avr_path)

    command = ["python", "avr.py", str(absolute_btor_path), "--bmc", "--witness", "-o", str(avr_output_path),  "--kmax", str(kmax)]
    
    if kind:
        command.append("--kind")

    start_mc = time.perf_counter()
    
    proc = subprocess.run(command, capture_output=True)
    
    end_mc = time.perf_counter()

    if proc.returncode:
        logger.error(proc.stderr.decode("utf-8"))
        logger.error(f"Error: avr failure for query '{label}'")
        return proc.returncode

    logger.info(f"done model checking in {end_mc-start_mc}s")

    avr_witness_path = [c for c in avr_results_path.glob("cex.witness")]
    btor_witness_path = absolute_btor_path.with_suffix(f".btor2.cex")
    
    avr_proof_path = [c for c in avr_results_path.glob("inv.txt")]

    os.chdir("..")
    if len(avr_witness_path) > 0:
        avr_witness_path[0].rename(str(btor_witness_path))
    else:
        btor_witness_path.touch()

    if len(avr_proof_path) > 0:
        avr_proof_path[0].rename(str(btor_witness_path.parent / "inv.txt"))

    logger.info(f"avr witness created at {btor_witness_path}")

    return 0


def model_check(
    input_path: Path, 
    output_path: Path, 
    model_checker: str, 
    sortcheck: Optional[str],
    catbtor: Optional[str],
    copyback: bool,
    fulltrace: bool,
    int_width: int,
    kmax: int,
    kind: bool,
    cpp: bool,
    debug: bool,
) -> int:
    # TODO: btorsim may be useful for getting full witnesses -- as is it actually
    # does not output valid witness output (header is missing), so we don't use it.
    # NOTE: for a model checker like avr, this might be necessary for full traces
    if not input_path.is_file():
        logger.error(f"Error: source is not a file ({input_path})")
        return 1

    rmdir(output_path, False)
    cleandir(WORK_DIR, True)

    src_path = WORK_DIR / input_path.name
    btor2_output_path = WORK_DIR / "btor2" 
    mcil_witness_path = WORK_DIR / input_path.with_suffix(".mcil.witness").name
    mcil_witness_pickle_path = WORK_DIR / input_path.with_suffix(".mcil.witness.pickle").name
    nuxmv_witness_path = WORK_DIR / input_path.with_suffix(".smv.witness").name

    if input_path.suffix == ".smv":
        witness_path = nuxmv_witness_path
    else:
        witness_path = mcil_witness_path

    shutil.copy(str(input_path), str(src_path))

    start_total = time.perf_counter()

    command = [
        "python3", str(DEFAULT_TRANSLATE), str(src_path), "btor2", 
        "--output", str(btor2_output_path),
        "--validate", "--intwidth", str(int_width),
        "--pickle"
    ]
    if sortcheck:
        command.append("--sortcheck")
        command.append(sortcheck)
    if catbtor:
        command.append("--catbtor")
        command.append(catbtor)
    if copyback:
        command.append("--keep")
    if cpp:
        command.append("--cpp")
    if debug:
        command.append("--debug")

    proc = subprocess.run(command)

    if proc.returncode:
        logger.error(f"Error: translation failure for {input_path}")
        return proc.returncode
    
    for check_system_path in btor2_output_path.iterdir():
        for btor_path in check_system_path.glob("*.btor2"):
            if model_checker == "btormc":
                retcode = run_btormc(DEFAULT_BTORMC, btor_path, kmax, kind)
                if retcode:
                    return retcode
            elif model_checker == "avr":
                retcode = run_avr(DEFAULT_AVR, btor_path, kmax, kind)
                if retcode:
                    return retcode
            else:
                logger.error(f"Error: unsupported model checker {model_checker}")
                return 1

    retcode = btorwit2mcilwit(
        btor2_output_path, mcil_witness_path, 
        verbose=True, do_pickle=(input_path.suffix == ".smv")
    )

    if retcode:
        return retcode

    if input_path.suffix == ".smv":
        retcode = mcilwit2nuxmvwit(
            mcil_witness_pickle_path, nuxmv_witness_path
        )

        if retcode: 
            return retcode
        
    end_total = time.perf_counter()

    logger.info(f"end-to-end done in {end_total-start_total}s")

    if copyback:
        logger.info(f"wrote files to {output_path}")
    else:
        witness_path.replace(output_path)
        logger.info(f"wrote MCIL witness to {output_path}")
        rmdir(WORK_DIR, True)

    return 0


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("input", 
        help="input program to model check via translation to btor2")
    parser.add_argument("modelchecker", choices=["btormc", "avr"], 
        help="model checker to use")
    parser.add_argument("--output",  
        help="location of output check-system response")
    parser.add_argument("--copyback",  action="store_true",
        help="copy all intermediate translations and results to output location")
    parser.add_argument("--intwidth", default=32, type=int, 
        help="bit width to translate Int types to")
    # parser.add_argument("--fulltrace", action="store_true", 
    #     help="return traces with all variable values for every state")
    parser.add_argument("--catbtor", help="path to catbtor for BTOR2 validation")
    parser.add_argument("--sortcheck", help="path to sortcheck.py for MCIL validation")
    parser.add_argument("--kmax", default=1000, type=int, 
        help="max bound for BMC")
    parser.add_argument("--kind", action="store_true", 
        help="enable k-induction")
    parser.add_argument("--cpp", action="store_true", 
        help="runs cpp on input if SMV")
    parser.add_argument("--debug", action="store_true", 
        help="output debug messages")
    parser.add_argument("--quiet", action="store_true", 
        help="silence output")
    args = parser.parse_args()

    if args.debug:
        logger.setLevel(logging.DEBUG)

    if args.quiet:
        pass

    input_path = Path(args.input)

    output_path = input_path.with_suffix(".witness")
    if args.output:
        output_path = Path(args.output)

    if args.copyback:
        WORK_DIR = output_path

    retcode = model_check(
        input_path=input_path, 
        output_path=output_path, 
        model_checker=args.modelchecker, 
        sortcheck=args.sortcheck,
        catbtor=args.catbtor,
        copyback=args.copyback, 
        fulltrace=True, 
        int_width=args.intwidth, 
        kmax=args.kmax,
        kind=args.kind,
        cpp=args.cpp,
        debug=args.debug
    )

    sys.exit(retcode)