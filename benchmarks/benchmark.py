"""Runs the benchmarks for te CAV 2024 paper.

For each .smv file in each in the directories relative to this script, runs the
selected solver (nuXmv, avr, btormc, pono) on each of the files, stores whether
that file was 'sat', 'unsat', 'timeout', 'memout', 'unknown' and its runtime,
and writes those results to a csv file along with the time of execution. 
"""
import multiprocessing as mp
import pathlib
import argparse
import sys
import subprocess
import time

from typing import Optional


FILE_NAME = pathlib.Path(__file__).name
FILE_DIR = pathlib.Path(__file__).parent

nuxmv_path = FILE_DIR / ".." / ".." / "nuXmv"
modelcheck_path = FILE_DIR / ".." / "modelcheck.py"
timeout: int = 3600
results_path = ""


def run_nuxmv(cmd: list[str]):
    file = cmd[-1]

    print(" ".join(cmd))

    try:
        start = time.perf_counter()
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
        end = time.perf_counter()
    except subprocess.TimeoutExpired:
        print(f"{file}: timeout")
        results = (f"{args.modelchecker}-{args.algorithm}", str(file), "timeout")
        with open(results_path, "a") as f:
            f.write('\t'.join(results) + "\n") 
        return

    if proc.stdout.find("is false") > 0:
        print(f"{file}: sat")
        results = (f"{args.modelchecker}-{args.algorithm}", str(file), "sat", str(end - start))
    elif proc.stdout.find("is true") > 0:
        print(f"{file}: unsat")
        results = (f"{args.modelchecker}-{args.algorithm}", str(file), "unsat", str(end - start))
    elif proc.returncode > 0:
        print(f"{file}: memout")
        results = (f"{args.modelchecker}-{args.algorithm}", str(file), "memout", str(end - start))
    else:
        print(f"{file}: unknown")
        results = (f"{args.modelchecker}-{args.algorithm}", str(file), "unknown", str(end - start))

    with open(results_path, "a") as f:
        f.write('\t'.join(results) + "\n") 


def run_modelcheck(cmd: list[str]):
    file = cmd[2]

    print(" ".join(cmd))

    start = time.perf_counter()
    proc = subprocess.run(cmd, capture_output=True, text=True)
    end = time.perf_counter()

    if end - start > timeout:
        print(f"{file}: timeout")
        results = (f"{args.modelchecker}-{args.algorithm}", str(file), "timeout")
    elif proc.stdout.find("unsat") >= 0:
        print(f"{file}: unsat")
        results = (f"{args.modelchecker}-{args.algorithm}", str(file), "unsat", str(end - start))
    elif proc.stdout.find("sat") >= 0:
        print(f"{file}: sat")
        results = (f"{args.modelchecker}-{args.algorithm}", str(file), "sat", str(end - start))
    elif proc.stdout.find("timeout") >= 0:
        print(f"{file}: timeout")
        results = (f"{args.modelchecker}-{args.algorithm}", str(file), "timeout")
    elif proc.returncode > 0:
        print(f"{file}: memout")
        results = (f"{args.modelchecker}-{args.algorithm}", str(file), "memout", str(end - start))
    else:
        print(f"{file}: unknown")
        results = (f"{args.modelchecker}-{args.algorithm}", str(file), "unknown", str(end - start))

    with open(results_path, "a") as f:
        f.write('\t'.join(results) + "\n") 


def benchmark(modelchecker: str, algorithm: str, nprocs: Optional[int]) -> int:
    if modelchecker == "nuxmv":
        args = [
            [
                str(nuxmv_path), 
                "-source", "nuxmv-bmc.cmd" if algorithm == "bmc" else "nuxmv-kind.cmd",
                str(file)
            ]
            for file in FILE_DIR.rglob("*.smv")
        ]

        # passing None here means we use cpu_count processes
        with mp.Pool(nprocs) as pool:
            pool.map(run_nuxmv, args)
    elif modelchecker == "btormc":
        if algorithm == "kind":
            print("kind unsupported for btormc")
            return 1
        
        args = [
            [
                "python3", str(modelcheck_path), 
                str(file), "btormc",
                "--no-witness", "--quiet",
                "--timeout", str(timeout)
            ]
            for file in FILE_DIR.rglob("*.smv")
        ]

        # passing None here means we use cpu_count processes
        with mp.Pool(nprocs) as pool:
            pool.map(run_modelcheck, args)
    elif modelchecker == "avr":
        args = [
            [
                "python3", str(modelcheck_path), 
                str(file), "avr",
                "--no-witness", "--quiet",
                "--timeout", str(timeout)
            ] + (["--kind"] if algorithm == "kind" else [])
            for file in FILE_DIR.rglob("*.smv")
        ]

        # passing None here means we use cpu_count processes
        with mp.Pool(nprocs) as pool:
            pool.map(run_modelcheck, args)
    elif modelchecker == "pono":
        args = [
            [
                "python3", str(modelcheck_path), 
                str(file), "pono", 
                "--no-witness", "--quiet",
                "--timeout", str(timeout)
            ] + (["--kind"] if algorithm == "kind" else [])
            for file in FILE_DIR.rglob("*.smv")
        ]

        # passing None here means we use cpu_count processes
        with mp.Pool(nprocs) as pool:
            pool.map(run_modelcheck, args)
    else:
        print("model checker not recognized")
        return 1
    
    return 0

if __name__ == "__main__":
    parser = argparse.ArgumentParser()

    parser.add_argument("modelchecker", choices=["nuxmv", "btormc", "avr", "pono"], 
        help="model checker to use")
    parser.add_argument("algorithm", choices=["bmc", "kind"], 
        help="model checking algorithm to benchmark")
    
    parser.add_argument("--results", help="file to output results")
    
    parser.add_argument("--nprocs",
        help="number of processors to run with (default=MAX)")
    parser.add_argument("--timeout", default=3600, type=int, 
        help="timeout in seconds for each test (default=3600)")
    
    args = parser.parse_args()

    if args.results:
        results_path = args.results
    else:
        results_path = f"{args.modelchecker}-{args.algorithm}.csv"

    if args.nprocs:
        nprocs = int(args.nprocs)
    else:
        nprocs = None

    timeout = args.timeout

    retcode = benchmark(args.modelchecker, args.algorithm, nprocs)

    sys.exit(retcode)