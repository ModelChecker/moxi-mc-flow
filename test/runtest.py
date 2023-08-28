from __future__ import annotations
from ctypes.wintypes import WORD
from glob import glob
from pathlib import Path
from typing import Any

import argparse
import shutil
import sys
import tomllib
import os
import subprocess
import logging

from logger import toplevel_logger, Color, Formatter, ColorFormatter


TEST_DIR = Path(__file__).parent
SUITES_DIR = TEST_DIR / "suites"
FILES_DIR = TEST_DIR / "inputs"
WORK_DIR = TEST_DIR / "__workdir"


def cleandir(dir: Path, quiet: bool):
    """Remove and create fresh dir, print a warning if quiet is False"""
    if dir.is_file():
        if not quiet:
            toplevel_logger.warning(f"Overwriting '{dir}'")
        os.remove(dir)
    elif dir.is_dir():
        if not quiet:
            toplevel_logger.warning(f"Overwriting '{dir}'")
        shutil.rmtree(dir)

    os.mkdir(dir)


def mkdir(dir: Path, quiet: bool):
    """Remove dir if it is a file then create dir, print a warning if quiet is False"""
    if dir.is_file():
        if not quiet:
            toplevel_logger.warning(f"Overwriting '{dir}'")
        os.remove(dir)

    if not os.path.isdir(dir):
        os.mkdir(dir)


class TestCase():

    def __init__(self, 
                 suite_name: str, 
                 test_name: str, 
                 top_results_dir: Path):
        self.status = True
        self.suite_name: str = suite_name
        self.test_name: str = test_name
        self.top_results_dir: Path = top_results_dir
        self.suite_results_dir: Path = top_results_dir / suite_name
        self.test_results_dir: Path = self.suite_results_dir / test_name

        # TODO: configure test file here

        self.clean()
        self.configure_logger()

    def clean(self):
        cleandir(self.test_results_dir, False)

    def configure_logger(self):
        self.logger = logging.getLogger(f"{__name__}_{self.suite_name}_{self.test_name}")
        self.logger.setLevel(logging.DEBUG)

        # note the order matters here -- if we add file_handler first the color
        # gets disabled...unsure why
        stream_handler = logging.StreamHandler(sys.stdout)
        stream_handler.setLevel(logging.DEBUG)
        stream_handler.setFormatter(ColorFormatter())
        self.logger.addHandler(stream_handler)

        file_handler = logging.FileHandler(f"{self.test_results_dir}/{self.test_name}.log")
        file_handler.setLevel(logging.DEBUG)
        file_handler.setFormatter(Formatter())
        self.logger.addHandler(file_handler)

    def test_fail(self, msg: str):
        self.logger.info(f"{self.test_name} [{Color.FAIL}FAIL{Color.ENDC}] {msg}")
        self.status = False

    def test_pass(self, msg: str):
        self.logger.info(f"{self.test_name} [{Color.PASS}PASS{Color.ENDC}] {msg}")

    def run(self, program: Path, copyback: bool):
        """CHANGE ME!"""
        os.chdir(WORK_DIR)

        proc = subprocess.run([program], capture_output=True)

        if proc.stdout != b"":
            with open(self.test_results_dir / f"{program.stem}.stdout", "wb") as f:
                f.write(proc.stdout)

        if proc.stderr != b"":
            with open(self.test_results_dir / f"{program.stem}.stderr", "wb") as f:
                f.write(proc.stderr)

        if proc.returncode != 0:
            self.test_fail(f"{program} returned with code {proc.returncode}")
            return

        # do more testing

        if self.status:
            self.test_pass("")

        if copyback:
            # copy source/temp files into results directory
            pass

        for f in glob(f"{WORK_DIR}/*"):
            os.remove(f)


class TestSuite():

    def __init__(self, name: str, top_results_dir: Path) -> None:
        """Initialize TestSuite by cleaning directories and loading TOML data."""
        self.status: bool = True
        self.suite_name: str = name
        self.tests: list[TestCase] = []
        self.top_results_dir: Path = top_results_dir
        self.suite_results_dir: Path = top_results_dir / name
        
        self.clean()
        self.configure_logger()
        self.configure_tests()

    def clean(self):
        """Clean/create work, results, and suite results directories. 
        Must run this before calling get_suite_logger."""
        cleandir(WORK_DIR, True)
        mkdir(self.top_results_dir, False)
        cleandir(self.suite_results_dir, False)

    def configure_logger(self):
        self.logger = logging.getLogger(f"{__name__}_{self.suite_name}")
        self.logger.setLevel(logging.DEBUG)

        # note the order matters here -- if we add file_handler first the color
        # gets disabled...unsure why
        stream_handler = logging.StreamHandler(sys.stdout)
        stream_handler.setLevel(logging.DEBUG)
        stream_handler.setFormatter(ColorFormatter())
        self.logger.addHandler(stream_handler)

        file_handler = logging.FileHandler(f"{self.suite_results_dir}/{self.suite_name}.log")
        file_handler.setLevel(logging.DEBUG)
        file_handler.setFormatter(Formatter())
        self.logger.addHandler(file_handler)

    def suite_fail_msg(self, msg: str):
        self.logger.error(msg)
        self.logger.info(f"Suite {self.suite_name} finished with status {Color.BOLD}{Color.FAIL}FAIL{Color.ENDC}")

    def suite_fail(self):
        self.logger.info(f"Suite {self.suite_name} finished with status {Color.BOLD}{Color.FAIL}FAIL{Color.ENDC}")

    def suite_pass(self):
        self.logger.info(f"Suite {self.suite_name} finished with status {Color.BOLD}{Color.PASS}PASS{Color.ENDC}")

    def configure_tests(self):
        """CHANGE ME! Configure test suite according to TOML file."""
        config_file = SUITES_DIR / f"{self.suite_name}.toml"

        if not config_file.is_file():
            self.suite_fail_msg(f"Suite configuration file '{config_file}' does not exist")
            return

        with open(config_file, "rb") as f:
            config: dict[str, Any] = tomllib.load(f)

        if "options" in config:
            pass

        if "test" not in config:
            return

        

    def run(self, program: Path, copyback: bool):
        """CHANGE ME!"""
        if not program.is_file():
            self.suite_fail_msg(f"Program `{program}` is not a valid executable.")
            return

        if not self.status:
            return

        for test in self.tests:
            test.run(program, copyback)
            self.status = test.status and self.status

        if not self.status:
            self.suite_fail()
        else:
            self.suite_pass()


def main(program: Path, 
         results_dir: Path, 
         suite_names: list[str],
         copyback: bool):
    """Runs `program` on each suite in `suite_names` and stores results in `results_dir`."""
    suites: list[TestSuite] = []
    for suite_name in suite_names:
        suites.append(TestSuite(suite_name, results_dir))

    for suite in suites:
        suite.run(program, copyback)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("program",
                        help="program to test")
    parser.add_argument("resultsdir",
                        help="directory to output test logs and copyback data")
    parser.add_argument("suites", nargs="+",
                        help="names of test suites to run; should be names of .toml files in suites/")
    parser.add_argument("--copyback", action="store_true",
                        help="copy all source, compiled, and log files from each testcase")
    args = parser.parse_args()

    main(Path(args.program), Path(args.resultsdir), args.suites, args.copyback)
