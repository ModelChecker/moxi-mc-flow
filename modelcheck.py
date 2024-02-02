import argparse
import pathlib
import subprocess
import sys
import os
import shutil
import time
from typing import Optional

from src import btorwit2moxiwit, moxiwit2nuxmvwit, util, log

FILE_NAME = pathlib.Path(__file__).name
FILE_DIR = pathlib.Path(__file__).parent
WORK_DIR = FILE_DIR / "__workdir__"

btormc_path = FILE_DIR / "boolector" / "build" / "bin" / "btormc"
avr_path = FILE_DIR / "avr"
translate_path = FILE_DIR / "translate.py"


def run_btormc(btormc_path: pathlib.Path, btor_path: pathlib.Path, timeout: int, kmax: int, kind: bool) -> int:
    log.info(f"Running btormc over {btor_path}", FILE_NAME)
    label = btor_path.stem

    command = [
        str(btormc_path), 
        str(btor_path), 
        "-kmax", str(kmax), 
        "--trace-gen-full",
    ]
    
    if kind:
        command.append("--kind")

    start_mc = time.perf_counter()

    try:
        proc = subprocess.run(command, capture_output=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        print("timeout")
        return 1
    
    end_mc = time.perf_counter()

    if proc.returncode:
        log.error(proc.stderr.decode("utf-8"), FILE_NAME)
        log.error(f"btormc failure for query '{label}'", FILE_NAME)
        return proc.returncode
    
    log.info(f"Done model checking in {end_mc-start_mc}s", FILE_NAME)

    btor_witness_bytes = proc.stdout

    btor_witness_path = btor_path.with_suffix(".btor2.cex")
    with open(btor_witness_path, "wb") as f:
        f.write(btor_witness_bytes)

    if btor_witness_bytes:
        print("sat")
    else:
        print("unsat")

    log.info(f"btormc witness created at {btor_witness_path}", FILE_NAME)

    return 0


def run_avr(avr_path: pathlib.Path, btor_path: pathlib.Path, timeout: int, kmax: int, kind: bool) -> int:
    absolute_btor_path = btor_path.absolute()

    log.info(f"Running avr over {absolute_btor_path}", FILE_NAME)
    label = absolute_btor_path.stem

    avr_output_path = absolute_btor_path.parent
    avr_results_path = avr_output_path / "work_test"

    os.chdir(avr_path)

    command = [
        "python3", 
        "avr.py", str(absolute_btor_path), 
        "--witness", 
        "-o", str(avr_output_path),  
        "--kmax", str(kmax), 
        "--timeout", str(timeout + 10)
    ]
    
    if kind:
        command.append("--kind")
    else:
        command.append("--bmc")

    start_mc = time.perf_counter()

    try:
        proc = subprocess.run(command, capture_output=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        print("timeout")
        return 1
    
    end_mc = time.perf_counter()

    if proc.returncode:
        log.error(proc.stderr.decode("utf-8"), FILE_NAME)
        log.error(f"AVR failure for query '{label}'", FILE_NAME)
        return proc.returncode

    log.info(f"Done model checking in {end_mc-start_mc}s", FILE_NAME)

    with open(str(avr_results_path / "result.pr"), "r") as f:
        result_str = f.read()

    if result_str == "avr-v":
        print("sat")
    elif result_str == "avr-h":
        print("unsat")
    else:
        print("crash")
        return 1

    avr_witness_path = [c for c in avr_results_path.glob("cex.witness")]
    btor_witness_path = absolute_btor_path.with_suffix(".btor2.cex")
    
    avr_proof_path = [c for c in avr_results_path.glob("inv.txt")]

    os.chdir("..")
    if len(avr_witness_path) > 0:
        avr_witness_path[0].rename(str(btor_witness_path))
    else:
        btor_witness_path.touch()

    if len(avr_proof_path) > 0:
        avr_proof_path[0].rename(str(btor_witness_path.parent / "inv.txt"))

    log.info(f"AVR witness created at {btor_witness_path}", FILE_NAME)

    return 0


def model_check(
    input_path: pathlib.Path, 
    output_path: pathlib.Path, 
    model_checker: str, 
    sortcheck: Optional[str],
    catbtor: Optional[str],
    copyback: bool,
    fulltrace: bool,
    int_width: int,
    timeout: int,
    kmax: int,
    kind: bool,
    cpp: bool,
    overwrite: bool,
    debug: bool,
) -> int:
    # TODO: btorsim may be useful for getting full witnesses -- as is it actually
    # does not output valid witness output (header is missing), so we don't use it.
    # NOTE: for a model checker like avr, this might be necessary for full traces
    if not input_path.is_file():
        log.error(f"Source is not a file ({input_path})", FILE_NAME)
        return 1
    
    status = util.cleandir(output_path, overwrite)
    if not status:
        return 1
    util.cleandir(WORK_DIR, True)

    src_path = WORK_DIR / input_path.name
    btor2_output_path = WORK_DIR / "btor2" 
    moxi_path = WORK_DIR / input_path.with_suffix(".moxi").name
    moxi_witness_path = WORK_DIR / input_path.with_suffix(".moxi.witness").name
    moxi_witness_pickle_path = WORK_DIR / input_path.with_suffix(".moxi.witness.pickle").name
    nuxmv_witness_path = WORK_DIR / input_path.with_suffix(".smv.witness").name

    if input_path.suffix == ".smv":
        witness_path = nuxmv_witness_path
    else:
        witness_path = moxi_witness_path

    shutil.copy(str(input_path), str(src_path))

    start_total = time.perf_counter()

    command = [
        "python3", str(translate_path), str(src_path), "btor2", 
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
        command.append(str(moxi_path))
    if cpp:
        command.append("--cpp")
    if debug:
        command.append("--debug")

    log.info(f"Translating {input_path}", FILE_NAME)
    proc = subprocess.run(command, capture_output=not debug)

    if proc.returncode:
        log.error(proc.stderr.decode("utf-8")[:-1], FILE_NAME) # [:-1] removes trailing "\n"
        log.error(f"Translation failure for {input_path}", FILE_NAME)
        return proc.returncode
    
    for check_system_path in btor2_output_path.iterdir():
        for btor_path in check_system_path.glob("*.btor2"):
            if model_checker == "btormc":
                retcode = run_btormc(btormc_path, btor_path, timeout, kmax, kind)
                if retcode:
                    return retcode
            elif model_checker == "avr":
                retcode = run_avr(avr_path, btor_path, timeout, kmax, kind)
                if retcode:
                    return retcode
            else:
                log.error(f"Unsupported model checker {model_checker}", FILE_NAME)
                return 1

    retcode = btorwit2moxiwit.main(
        btor2_output_path, moxi_witness_path, 
        verbose=True, do_pickle=(input_path.suffix == ".smv"),
        overwrite=overwrite
    )

    if retcode:
        return retcode

    if input_path.suffix == ".smv":
        retcode = moxiwit2nuxmvwit.main(
            moxi_witness_pickle_path, nuxmv_witness_path,
            overwrite=overwrite
        )

        if retcode: 
            return retcode
        
    end_total = time.perf_counter()

    log.info(f"End-to-end done in {end_total-start_total}s", FILE_NAME)

    if copyback:
        shutil.copytree(WORK_DIR, output_path)
        log.info(f"Wrote files to {output_path}", FILE_NAME)
    else:
        witness_path.replace(output_path)
        log.info(f"Wrote witness to {output_path}", FILE_NAME)

    util.rmdir(WORK_DIR)

    return 0


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("input", 
        help="input program to model check via translation to btor2")
    parser.add_argument("modelchecker", choices=["btormc", "avr"], 
        help="model checker to use")
    parser.add_argument("--output",  
        help="location of output check-system response")
    parser.add_argument("--avr-path",
        help="path to avr directory")
    parser.add_argument("--btormc-path",  
        help="path to btormc binary")
    parser.add_argument("--translate-path",  
        help="path to translate.py script")
    parser.add_argument("--copyback",  action="store_true",
        help="copy all intermediate translations and results to output location")
    parser.add_argument("--intwidth", default=32, type=int, 
        help="bit width to translate Int types to (default=32)")
    # parser.add_argument("--fulltrace", action="store_true", 
    #     help="return traces with all variable values for every state")
    parser.add_argument("--catbtor", help="path to catbtor for BTOR2 validation")
    parser.add_argument("--sortcheck", help="path to sortcheck.py for MCIL validation")
    parser.add_argument("--kmax", default=1000, type=int, 
        help="max bound for BMC (default=1000)")
    parser.add_argument("--timeout", default=3600, type=int, 
        help="timeout in seconds (default=3600)")
    parser.add_argument("--kind", action="store_true", 
        help="enable k-induction")
    parser.add_argument("--cpp", action="store_true", 
        help="runs cpp on input if SMV")
    parser.add_argument("--debug", action="store_true", 
        help="output debug messages")
    parser.add_argument("--quiet", action="store_true", 
        help="silence output")
    parser.add_argument("--overwrite", action="store_true", 
        help="enable overwriting of output path")
    args = parser.parse_args()

    if args.debug:
        log.set_debug()

    if args.quiet:
        log.set_quiet()

    if args.avr_path:
        avr_path = pathlib.Path(args.avr_path)

    if args.btormc_path:
        btormc_path = pathlib.Path(args.btormc_path)

    if args.translate_path:
        translate_path = pathlib.Path(args.translate_path)

    input_path = pathlib.Path(args.input)

    output_path = input_path.with_suffix(".witness")
    if args.output:
        output_path = pathlib.Path(args.output)
        
    WORK_DIR = FILE_DIR / f"__workdir__{input_path.name}"

    retcode = model_check(
        input_path=input_path, 
        output_path=output_path, 
        model_checker=args.modelchecker, 
        sortcheck=args.sortcheck,
        catbtor=args.catbtor,
        copyback=args.copyback, 
        fulltrace=True, 
        int_width=args.intwidth, 
        timeout=args.timeout,
        kmax=args.kmax,
        kind=args.kind,
        cpp=args.cpp,
        overwrite=args.overwrite,
        debug=args.debug
    )

    sys.exit(retcode)
