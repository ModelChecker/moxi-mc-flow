import argparse
import pathlib
import subprocess
import sys
import os
import shutil
import time
import tempfile
from typing import Optional

from src import btorwit2moxiwit, moxiwit2nuxmvwit, log

FILE_NAME = pathlib.Path(__file__).name
FILE_DIR = pathlib.Path(__file__).parent

btormc_path = FILE_DIR / "deps" / "btormc"
avr_path = FILE_DIR / "deps" / "avr"
pono_path = FILE_DIR / "deps" / "pono" 
translate_path = FILE_DIR / "translate.py"


def run_btormc(btormc_path: pathlib.Path, btor_path: pathlib.Path, timeout: int, kmax: int, kind: bool) -> int:
    log.debug(1, f"Running btormc over {btor_path}", FILE_NAME)
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
    
    log.debug(1, f"Done model checking in {end_mc-start_mc}s", FILE_NAME)

    btor_witness_bytes = proc.stdout

    btor_witness_path = btor_path.with_suffix(".btor2.cex")
    with open(btor_witness_path, "wb") as f:
        f.write(btor_witness_bytes)

    if btor_witness_bytes.startswith(b'sat'):
        print("sat")
        log.debug(1, f"btormc witness created at {btor_witness_path}", FILE_NAME)
    elif btor_witness_bytes.startswith(b'unsat'):
        print("unsat")
    else:
        print("unknown")

    log.debug(1, f"btormc witness created at {btor_witness_path}", FILE_NAME)

    return 0


def run_avr(avr_path: pathlib.Path, btor_path: pathlib.Path, timeout: int, kmax: int, kind: bool) -> int:
    absolute_btor_path = btor_path.absolute()

    log.debug(1, f"Running avr over {absolute_btor_path}", FILE_NAME)
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

    log.debug(1, f"Done model checking in {end_mc-start_mc}s", FILE_NAME)

    with open(str(avr_results_path / "result.pr"), "r") as f:
        result_str = f.read()

    btor_witness_path = absolute_btor_path.with_suffix(".btor2.cex")
    os.chdir("..")

    if result_str == "avr-v":
        print("sat")
        avr_witness_path = [c for c in avr_results_path.glob("cex.witness")]
        avr_witness_path[0].rename(str(btor_witness_path))
    elif result_str == "avr-h":
        print("unsat")
        avr_proof_path = [c for c in avr_results_path.glob("inv.txt")]
        if len(avr_proof_path) > 0:
            avr_proof_path[0].rename(str(btor_witness_path.parent / "inv.txt"))
        with open(str(btor_witness_path), "w") as f:
            f.write("unsat")
    else:
        print("crash")
        btor_witness_path.touch()
        return 1

    log.debug(1, f"AVR witness created at {btor_witness_path}", FILE_NAME)

    return 0


def run_pono(pono_path: pathlib.Path, btor_path: pathlib.Path, timeout: int, kmax: int, kind: bool) -> int:
    log.debug(1, f"Running pono over {btor_path}", FILE_NAME)
    # label = btor_path.stem

    command = [str(pono_path), "-k", str(kmax), "-e"]
    if kind:
        command.append("ind")
    else:
        command.append("bmc")
    command.append(str(btor_path))

    start_mc = time.perf_counter()

    try:
        proc = subprocess.run(command, capture_output=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        print("timeout")
        return 1

    end_mc = time.perf_counter()

    log.debug(1, f"Done model checking in {end_mc-start_mc}s", FILE_NAME)

    btor_witness_bytes = proc.stdout
    btor_witness_path = btor_path.with_suffix(".btor2.cex")

    if btor_witness_bytes.startswith(b'sat'):
        print("sat")
        with open(btor_witness_path, "wb") as f:
            f.write(btor_witness_bytes)
    elif btor_witness_bytes.startswith(b'unsat'):
        print("unsat")
        with open(btor_witness_path, "wb") as f:
            f.write(btor_witness_bytes)
    else:
        print("unknown")
        btor_witness_path.touch()

    return 0


def model_check(
    input_path: pathlib.Path, 
    output_path: pathlib.Path, 
    workdir: pathlib.Path,
    model_checker: str, 
    sortcheck: Optional[str],
    catbtor: Optional[str],
    copyback: bool,
    witness: bool,
    int_width: int,
    timeout: int,
    kmax: int,
    kind: bool,
    cpp: bool,
    debug: int,
    overwrite: bool,
) -> int:
    # TODO: btorsim may be useful for getting full witnesses -- as is it actually
    # does not output valid witness output (header is missing), so we don't use it.
    # NOTE: for a model checker like avr/pono, this might be necessary for full traces
    if not input_path.is_file():
        log.error(f"Source is not a file ({input_path})", FILE_NAME)
        return 1

    if (copyback or witness) and output_path.exists():
        if not overwrite:
            log.error(f"Output path '{output_path}' already exists.", FILE_NAME)
            return 1
    
        if output_path.is_file():
            output_path.unlink()
        elif output_path.is_dir():
            shutil.rmtree(output_path)
    
    src_path = workdir / input_path.name
    btor2_output_path = workdir / "btor2" 
    moxi_path = workdir / input_path.with_suffix(".moxi").name
    moxi_witness_path = workdir / input_path.with_suffix(".moxi.witness").name
    moxi_witness_pickle_path = workdir / input_path.with_suffix(".moxi.witness.pickle").name
    nuxmv_witness_path = workdir / input_path.with_suffix(".smv.witness").name

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
        command.append(str(debug))

    log.debug(1, f"Translating {input_path}", FILE_NAME)

    try:
        proc = subprocess.run(command, capture_output=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        print("timeout")
        return 1

    end_translate = time.perf_counter()
    time_elapsed = end_translate - start_total

    if debug:
        print(proc.stderr.decode())

    if proc.returncode:
        if not debug:
            log.error(proc.stderr.decode("utf-8")[:-1], FILE_NAME) # [:-1] removes trailing "\n"
        log.error(f"Translation failure for {input_path}", FILE_NAME)
        return proc.returncode
    
    for check_system_path in btor2_output_path.iterdir():
        for btor_path in check_system_path.glob("*.btor2"):
            if model_checker == "btormc":
                retcode = run_btormc(btormc_path, btor_path, int(timeout - time_elapsed), kmax, kind)
                if retcode:
                    return retcode
            elif model_checker == "avr":
                retcode = run_avr(avr_path, btor_path, int(timeout - time_elapsed), kmax, kind)
                if retcode:
                    return retcode
            elif model_checker == "pono":
                retcode = run_pono(pono_path, btor_path, int(timeout - time_elapsed), kmax, kind)
                if retcode:
                    return retcode
            else:
                log.error(f"Unsupported model checker {model_checker}", FILE_NAME)
                return 1

    retcode = btorwit2moxiwit.main(
        btor2_output_path, moxi_witness_path, 
        verbose=True, do_pickle=(input_path.suffix == ".smv"),
    )

    if retcode:
        return retcode

    if input_path.suffix == ".smv":
        retcode = moxiwit2nuxmvwit.main(
            moxi_witness_pickle_path, nuxmv_witness_path,
        )

        if retcode: 
            return retcode
        
    end_total = time.perf_counter()

    log.debug(1, f"End-to-end done in {end_total-start_total}s", FILE_NAME)

    if copyback:
        shutil.copytree(workdir, output_path)
        log.debug(1, f"Wrote files to {output_path}", FILE_NAME)
    elif witness:
        shutil.copy(witness_path, output_path)
        log.debug(1, f"Wrote witness to {output_path}", FILE_NAME)

    return 0


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("input", 
        help="input program to model check via translation to btor2")
    parser.add_argument("modelchecker", choices=["btormc", "avr", "pono"], 
        help="model checker to use")
    parser.add_argument("--output",  
        help="location of output check-system response")
    parser.add_argument("--no-witness", action="store_true",
        help="disable writing of witness file")
    parser.add_argument("--avr-path",
        help="path to avr directory")
    parser.add_argument("--btormc-path",  
        help="path to btormc binary")
    parser.add_argument("--pono-path",
        help="path to pono binary")
    parser.add_argument("--translate-path",  
        help="path to translate.py script")
    parser.add_argument("--copyback",  action="store_true",
        help="copy all intermediate translations and results to output location")
    parser.add_argument("--intwidth", default=32, type=int, 
        help="bit width to translate Int types to (default=32)")
    parser.add_argument("--catbtor", help="path to catbtor for BTOR2 validation")
    parser.add_argument("--sortcheck", help="path to sortcheck.py for MoXI validation")
    parser.add_argument("--kmax", default=1000, type=int, 
        help="max bound for BMC (default=1000)")
    parser.add_argument("--timeout", default=3600, type=int, 
        help="timeout in seconds for model checker (default=3600)")
    parser.add_argument("--kind", action="store_true", 
        help="enable k-induction")
    parser.add_argument("--cpp", action="store_true", 
        help="runs cpp on input if SMV")
    parser.add_argument("--quiet", action="store_true", 
        help="silence output")
    parser.add_argument(
        "--debug",
        nargs="?",
        default=0,
        const=1,
        type=int,
        help="set debug level (0=none, 1=basic, 2=extra)",
    )
    parser.add_argument("--overwrite", action="store_true", 
        help="enable overwriting of output location")
    args = parser.parse_args()

    log.set_debug_level(args.debug)

    if args.quiet:
        log.set_quiet()

    if args.avr_path:
        avr_path = pathlib.Path(args.avr_path)

    if args.btormc_path:
        btormc_path = pathlib.Path(args.btormc_path)

    if args.pono_path:
        pono_path = pathlib.Path(args.pono_path)

    if args.translate_path:
        translate_path = pathlib.Path(args.translate_path)

    input_path = pathlib.Path(args.input)

    output_path = input_path.with_suffix(".witness").absolute()
    if args.output:
        output_path = pathlib.Path(args.output).absolute()
        
    with tempfile.TemporaryDirectory() as workdir_name:
        workdir = pathlib.Path(workdir_name)
        retcode = model_check(
            input_path=input_path, 
            output_path=output_path, 
            workdir=workdir,
            model_checker=args.modelchecker, 
            sortcheck=args.sortcheck,
            catbtor=args.catbtor,
            copyback=args.copyback, 
            witness=not args.no_witness, 
            int_width=args.intwidth, 
            timeout=args.timeout,
            kmax=args.kmax,
            kind=args.kind,
            cpp=args.cpp,
            debug=args.debug,
            overwrite=args.overwrite
        )

    sys.exit(retcode)
