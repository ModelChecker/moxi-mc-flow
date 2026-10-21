#!/usr/bin/env python3
import argparse
import pathlib
import signal
import subprocess
import sys
import os
import shutil
import time
import tempfile
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from typing import Optional

from src import btorwit2moxiwit, moxiwit2nuxmvwit, log

FILE_NAME = pathlib.Path(__file__).name
FILE_DIR = pathlib.Path(__file__).parent
VERSION = "svcomp27"

btormc_path = FILE_DIR / "deps" / "btormc"
avr_path = FILE_DIR / "deps" / "avr"
pono_path = FILE_DIR / "deps" / "pono"
ric3_path = FILE_DIR / "deps" / "ric3"
translate_path = FILE_DIR / "translate.py"

SOLVERS = {"btormc", "avr", "pono", "ric3"}
ALGORITHMS = {"bmc", "kind", "ic3"}
# ic3sa handles bit-vectors and arrays. ic3bits/mbic3 reject arrays, and ic3ia
# returned unknown on some SAT queries (e.g. Delay.moxi).
PONO_ENGINES = {"bmc": "bmc", "kind": "ind", "ic3": "ic3sa"}
RIC3_ENGINES = {"bmc": "bmc", "kind": "kind", "ic3": "ic3"}
# btormc has no IC3 engine. Its k-induction implementation is also buggy:
# https://github.com/Boolector/boolector/issues/220
UNSUPPORTED = {("btormc", "kind"), ("btormc", "ic3")}

# Portfolio order from greedy complementary coverage
# The first six jobs cover every instance any non-btormc engine solved; later jobs only race SAT times.
PORTFOLIO_JOBS = [
    {"solver": "ric3", "algorithm": "ic3"},
    {"solver": "ric3", "algorithm": "kind"},
    {"solver": "avr", "algorithm": "ic3"},
    {"solver": "pono", "algorithm": "ic3"},
    {"solver": "ric3", "algorithm": "bmc"},
    {"solver": "pono", "algorithm": "kind"},
    {"solver": "pono", "algorithm": "bmc"},
    {"solver": "avr", "algorithm": "bmc"},
    {"solver": "avr", "algorithm": "kind"},
]


def available_cores() -> int:
    try:
        n = len(os.sched_getaffinity(0))
    except (AttributeError, OSError):
        n = os.cpu_count()
    return n if n and n > 0 else 1


def run_btormc(btormc_path: pathlib.Path, btor_path: pathlib.Path, timeout: int, kmax: int, algorithm: str) -> int:
    log.debug(1, f"Running btormc over {btor_path}", FILE_NAME)
    label = btor_path.stem

    if algorithm != "bmc":
        log.error(f"btormc does not support algorithm '{algorithm}'", FILE_NAME)
        return 1

    command = [
        str(btormc_path), 
        str(btor_path), 
        "--kmax", str(kmax),
        "--trace-gen-full",
    ]
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


def run_avr(avr_path: pathlib.Path, btor_path: pathlib.Path, timeout: int, kmax: int, algorithm: str) -> int:
    absolute_btor_path = btor_path.absolute()

    log.debug(1, f"Running avr over {absolute_btor_path}", FILE_NAME)
    label = absolute_btor_path.stem

    if algorithm not in ALGORITHMS:
        log.error(f"invalid algorithm for avr '{algorithm}'", FILE_NAME)
        return 1

    avr_output_path = absolute_btor_path.parent
    avr_results_path = avr_output_path / "work_test"

    # AVR looks up its workers relative to the process working directory.
    # Restore the caller's directory afterwards so the tool can be started
    # from any path (required by SV-COMP).
    previous_cwd = os.getcwd()
    os.chdir(avr_path)

    command = [
        "python3", 
        "avr.py", str(absolute_btor_path), 
        "--witness", 
        "-o", str(avr_output_path),  
        "--kmax", str(kmax), 
        "--timeout", str(timeout + 10)
    ]
    
    if algorithm == "kind":
        command.append("--kind")
    elif algorithm == "bmc":
        command.append("--bmc")
    # AVR's default engine is IC3; omit both --bmc and --kind.

    start_mc = time.perf_counter()

    try:
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
    finally:
        os.chdir(previous_cwd)

    log.debug(1, f"Done model checking in {end_mc-start_mc}s", FILE_NAME)

    with open(str(avr_results_path / "result.pr"), "r") as f:
        result_str = f.read()

    btor_witness_path = absolute_btor_path.with_suffix(".btor2.cex")

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


def run_pono(pono_path: pathlib.Path, btor_path: pathlib.Path, timeout: int, kmax: int, algorithm: str) -> int:
    log.debug(1, f"Running pono over {btor_path}", FILE_NAME)

    if algorithm not in PONO_ENGINES:
        log.error(f"invalid algorithm for pono '{algorithm}'", FILE_NAME)
        return 1

    command = [
        str(pono_path),
        "-k", str(kmax),
        "-e", PONO_ENGINES[algorithm],
        "--witness",
        str(btor_path),
    ]

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


def run_ric3(ric3_path: pathlib.Path, btor_path: pathlib.Path, timeout: int, kmax: int, algorithm: str) -> int:
    log.debug(1, f"Running ric3 over {btor_path}", FILE_NAME)
    label = btor_path.stem

    if algorithm not in RIC3_ENGINES:
        log.error(f"invalid algorithm for ric3 '{algorithm}'", FILE_NAME)
        return 1

    cert_path = btor_path.with_suffix(".ric3.cert")
    command = [
        str(ric3_path),
        "check",
        "--cert", str(cert_path),
        "--ui", "false",
        str(btor_path),
        RIC3_ENGINES[algorithm],
        "--end", str(kmax),
        "--time-limit", str(max(timeout, 1)),
    ]

    start_mc = time.perf_counter()

    try:
        proc = subprocess.run(command, capture_output=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        print("timeout")
        return 1

    end_mc = time.perf_counter()

    if proc.returncode:
        log.error(proc.stderr.decode("utf-8"), FILE_NAME)
        log.error(f"ric3 failure for query '{label}'", FILE_NAME)
        return proc.returncode

    log.debug(1, f"Done model checking in {end_mc-start_mc}s", FILE_NAME)

    result = None
    for line in proc.stdout.decode("utf-8", errors="replace").splitlines():
        if line in {"SAT", "UNSAT", "UNKNOWN"}:
            result = line

    btor_witness_path = btor_path.with_suffix(".btor2.cex")

    if result == "SAT" and cert_path.is_file():
        print("sat")
        cert_path.replace(btor_witness_path)
    elif result == "UNSAT":
        print("unsat")
        with open(btor_witness_path, "w") as f:
            f.write("unsat")
        cert_path.unlink(missing_ok=True)
    else:
        print("unknown")
        btor_witness_path.touch()
        cert_path.unlink(missing_ok=True)

    log.debug(1, f"ric3 witness created at {btor_witness_path}", FILE_NAME)

    return 0


def kill_process_group(proc: subprocess.Popen) -> None:
    if proc.poll() is not None:
        return
    try:
        os.killpg(proc.pid, signal.SIGTERM)
    except ProcessLookupError:
        return
    try:
        proc.wait(timeout=2)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        proc.wait()


def portfolio_child_command(
    input_path: pathlib.Path,
    output_path: pathlib.Path,
    solver: str,
    algorithm: str,
    timeout: int,
    kmax: int,
    args: argparse.Namespace,
) -> list[str]:
    command = [
        sys.executable,
        str(FILE_DIR / "modelcheck.py"),
        str(input_path),
        solver,
        "--algorithm", algorithm,
        "--timeout", str(timeout),
        "--kmax", str(kmax),
        "--intwidth", str(args.intwidth),
        "--output", str(output_path),
        "--overwrite",
    ]
    if args.no_witness and not args.copyback:
        command.append("--no-witness")
    if args.copyback:
        command.append("--copyback")
    if args.cpp:
        command.append("--cpp")
    if args.quiet:
        command.append("--quiet")
    if args.debug:
        command.extend(["--debug", str(args.debug)])
    if args.sortcheck:
        command.extend(["--sortcheck", args.sortcheck])
    if args.catbtor:
        command.extend(["--catbtor", args.catbtor])
    if args.avr_path:
        command.extend(["--avr-path", args.avr_path])
    if args.btormc_path:
        command.extend(["--btormc-path", args.btormc_path])
    if args.pono_path:
        command.extend(["--pono-path", args.pono_path])
    if args.ric3_path:
        command.extend(["--ric3-path", args.ric3_path])
    if args.translate_path:
        command.extend(["--translate-path", args.translate_path])
    return command


def publish_portfolio_output(
    source: pathlib.Path,
    output_path: pathlib.Path,
    copyback: bool,
    witness: bool,
    overwrite: bool,
) -> int:
    if not copyback and not witness:
        return 0
    if not source.exists():
        return 0
    if output_path.exists():
        if not overwrite:
            log.error(f"Output path '{output_path}' already exists.", FILE_NAME)
            return 1
        if output_path.is_file():
            output_path.unlink()
        elif output_path.is_dir():
            shutil.rmtree(output_path)
    if copyback:
        shutil.copytree(source, output_path)
        log.debug(1, f"Wrote files to {output_path}", FILE_NAME)
    elif source.is_file():
        shutil.copy(source, output_path)
        log.debug(1, f"Wrote witness to {output_path}", FILE_NAME)
    return 0


def portfolio_verdict(stdout: str) -> Optional[str]:
    for line in stdout.splitlines()[::-1]:
        if line.startswith("unsat"):
            return "unsat"
        if line.startswith("sat"):
            return "sat"
    return None


def run_portfolio(
    input_path: pathlib.Path,
    output_path: pathlib.Path,
    jobs: list[dict],
    nprocs: int,
    args: argparse.Namespace,
) -> int:
    jobs = jobs[:nprocs]
    if not jobs:
        log.error("portfolio has no jobs to run", FILE_NAME)
        return 1

    log.debug(
        1,
        f"Running portfolio of {len(jobs)} processes on {nprocs} cores",
        FILE_NAME,
    )

    with tempfile.TemporaryDirectory() as tmp_name:
        tmp = pathlib.Path(tmp_name)
        children = []
        winner = None
        returncode = 1
        try:
            for job in jobs:
                solver = job["solver"]
                algorithm = job["algorithm"]
                label = f"{solver}-{algorithm}"
                job_dir = tmp / label
                job_dir.mkdir()
                if args.copyback:
                    child_output = job_dir / "out"
                else:
                    child_output = job_dir / "witness"

                command = portfolio_child_command(
                    input_path,
                    child_output,
                    solver,
                    algorithm,
                    int(job.get("timeout", args.timeout)),
                    int(job.get("kmax", args.kmax)),
                    args,
                )
                log.debug(2, " ".join(command), FILE_NAME)

                stdout_path = job_dir / "stdout"
                stderr_path = job_dir / "stderr"
                stdout_file = open(stdout_path, "wb")
                stderr_file = open(stderr_path, "wb")
                try:
                    proc = subprocess.Popen(
                        command,
                        stdout=stdout_file,
                        stderr=stderr_file,
                        start_new_session=True,
                    )
                finally:
                    stdout_file.close()
                    stderr_file.close()

                children.append({
                    "label": label,
                    "proc": proc,
                    "stdout_path": stdout_path,
                    "stderr_path": stderr_path,
                    "output": child_output,
                    "timeout": int(job.get("timeout", args.timeout)),
                })

            if not children:
                log.error("failed to start any portfolio process", FILE_NAME)
                return 1

            grace = max(child["timeout"] for child in children) + 30
            with ThreadPoolExecutor(max_workers=len(children)) as pool:
                try:
                    future_map = {
                        pool.submit(child["proc"].wait): child for child in children
                    }
                    pending = set(future_map)
                    deadline = time.monotonic() + grace
                    while pending:
                        remaining = deadline - time.monotonic()
                        if remaining <= 0:
                            print("timeout")
                            return 1
                        done, pending = wait(
                            pending, timeout=remaining, return_when=FIRST_COMPLETED
                        )
                        if not done:
                            print("timeout")
                            return 1
                        for future in done:
                            child = future_map[future]
                            child_returncode = future.result()
                            stdout = child["stdout_path"].read_text(
                                encoding="utf-8", errors="replace"
                            )
                            if portfolio_verdict(stdout) is None:
                                log.debug(
                                    1,
                                    f"portfolio ignoring non-decisive {child['label']}",
                                    FILE_NAME,
                                )
                                continue
                            winner = child
                            returncode = child_returncode
                            for leftover in pending:
                                kill_process_group(future_map[leftover]["proc"])
                            for leftover in pending:
                                leftover.result()
                            pending = set()
                            break
                finally:
                    for child in children:
                        kill_process_group(child["proc"])
        finally:
            for child in children:
                kill_process_group(child["proc"])

        if winner is None:
            print("unknown")
            return 1

        stdout = winner["stdout_path"].read_text(encoding="utf-8", errors="replace")
        stderr = winner["stderr_path"].read_text(encoding="utf-8", errors="replace")

        log.debug(1, f"portfolio winner: {winner['label']}", FILE_NAME)
        if stderr:
            sys.stderr.write(stderr)
        if stdout:
            sys.stdout.write(stdout)
            if not stdout.endswith("\n"):
                sys.stdout.write("\n")
        else:
            print("unknown")
            if returncode == 0:
                returncode = 1

        publish_ret = publish_portfolio_output(
            winner["output"],
            output_path,
            args.copyback,
            not args.no_witness,
            args.overwrite,
        )
        if publish_ret:
            return publish_ret

        return returncode if returncode is not None else 1


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
    algorithm: str,
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
    moxi_path = workdir / input_path.with_suffix(".out.moxi").name
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
    log.debug(2, " ".join(command), FILE_NAME)

    try:
        proc = subprocess.run(command, capture_output=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        print("timeout")
        return 1

    end_translate = time.perf_counter()
    time_elapsed = end_translate - start_total

    if debug:
        sys.stderr.write(proc.stderr.decode())

    if proc.returncode:
        if not debug:
            sys.stderr.write(proc.stderr.decode("utf-8"))
        log.error(f"Translation failure for {input_path}", FILE_NAME)
        return proc.returncode
    
    if (model_checker, algorithm) in UNSUPPORTED:
        log.error(f"{model_checker} does not support algorithm '{algorithm}'", FILE_NAME)
        return 1

    for check_system_path in btor2_output_path.iterdir():
        for btor_path in check_system_path.glob("*.btor2"):
            if model_checker == "btormc":
                retcode = run_btormc(btormc_path, btor_path, int(timeout - time_elapsed), kmax, algorithm)
                if retcode:
                    return retcode
            elif model_checker == "avr":
                retcode = run_avr(avr_path, btor_path, int(timeout - time_elapsed), kmax, algorithm)
                if retcode:
                    return retcode
            elif model_checker == "pono":
                retcode = run_pono(pono_path, btor_path, int(timeout - time_elapsed), kmax, algorithm)
                if retcode:
                    return retcode
            elif model_checker == "ric3":
                retcode = run_ric3(ric3_path, btor_path, int(timeout - time_elapsed), kmax, algorithm)
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
    parser = argparse.ArgumentParser(
        description=(
            "Model check an SMV, MoXI, or JSON file. With no model checker "
            "argument, run a hard-coded portfolio of solvers/algorithms in "
            "parallel and stop at the first decisive sat/unsat result."
        )
    )
    parser.add_argument(
        "--version",
        action="version",
        version=VERSION,
        help="print the tool version and exit",
    )
    parser.add_argument("input",
        help="input program to model check via translation to btor2")
    parser.add_argument("modelchecker", nargs="?", choices=["btormc", "avr", "pono", "ric3"],
        help="model checker to use; omit to run the hard-coded portfolio")
    parser.add_argument("--algorithm", choices=["bmc", "kind", "ic3"],
        help="model-checking algorithm to use in single-solver mode (default: bmc)")
    parser.add_argument("--output",
        help="location of output check-system response")
    parser.add_argument("--no-witness", action="store_true",
        help="disable writing of witness file")
    parser.add_argument("--nprocs", type=int,
        help="parallel portfolio processes (default: all available CPU cores)")
    parser.add_argument("--avr-path",
        help="path to avr directory")
    parser.add_argument("--btormc-path",
        help="path to btormc binary")
    parser.add_argument("--pono-path",
        help="path to pono binary")
    parser.add_argument("--ric3-path",
        help="path to ric3 binary")
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
        help="enable k-induction (alias for --algorithm kind)")
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

    if args.ric3_path:
        ric3_path = pathlib.Path(args.ric3_path)

    if args.translate_path:
        translate_path = pathlib.Path(args.translate_path)

    input_path = pathlib.Path(args.input)

    output_path = input_path.with_suffix(".witness").absolute()
    if args.output:
        output_path = pathlib.Path(args.output).absolute()

    if args.modelchecker is None:
        nprocs = args.nprocs if args.nprocs is not None else available_cores()
        if nprocs < 1:
            log.error("nprocs must be at least 1", FILE_NAME)
            sys.exit(1)
        retcode = run_portfolio(input_path, output_path, PORTFOLIO_JOBS, nprocs, args)
        sys.exit(retcode)

    algorithm = args.algorithm
    if args.kind:
        if algorithm and algorithm != "kind":
            log.error(f"cannot combine --kind with --algorithm {algorithm}", FILE_NAME)
            sys.exit(1)
        algorithm = "kind"
    if not algorithm:
        algorithm = "bmc"

    with tempfile.TemporaryDirectory() as workdir_name:
        workdir = pathlib.Path(workdir_name)
        retcode = model_check(
            input_path=input_path,
            output_path=output_path,
            workdir=workdir,
            model_checker=args.modelchecker,
            algorithm=algorithm,
            sortcheck=args.sortcheck,
            catbtor=args.catbtor,
            copyback=args.copyback,
            witness=not args.no_witness,
            int_width=args.intwidth,
            timeout=args.timeout,
            kmax=args.kmax,
            cpp=args.cpp,
            debug=args.debug,
            overwrite=args.overwrite
        )

    sys.exit(retcode)
