from __future__ import annotations
from glob import glob
from pathlib import Path

import argparse
import shutil
import sys
import os
import subprocess
import logging

from logger import toplevel_logger, Color, Formatter, ColorFormatter

TEST_DIR = Path(__file__).parent
WORK_DIR = TEST_DIR / "__workdir__"
SMV_DIR = TEST_DIR / "smv"

SUITES = [ 
    {
        "name": "nuxmv2mcil",
        "source": "smv",
        "target": "mcil",
        "dir": "smv" 
    },
    {
        "name": "nuxmv2mcil-invgen",
        "source": "smv",
        "target": "mcil",
        "dir": "smv/nuxmv/invgen" 
    },
    {
        "name": "nuxmv2btor",
        "source": "smv",
        "target": "btor2",
        "dir": "smv" 
    },
    {
        "name": "mcil2btor",
        "source": "mcil",
        "target": "btor2",
        "dir": "mcil"
    }
]
SUITE_NAMES = [ suite["name"] for suite in SUITES ]
SUITE_NAME_MAP = { suite["name"]: suite for suite in SUITES }


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

    if not dir.is_dir():
        os.mkdir(dir)


class TestCase():

    def __init__(self, 
                 suite_name: str, 
                 test_name: str, 
                 test_path: Path, 
                 top_results_dir: Path):
        self.status = True
        self.suite_name: str = suite_name
        self.test_name: str = test_name
        self.test_path: Path = test_path
        self.top_results_dir: Path = top_results_dir
        self.suite_results_dir: Path = top_results_dir / suite_name
        self.test_results_dir: Path = self.suite_results_dir / test_name

        self.clean()
        print(f"configuring logger for {self.test_name}")
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

        file_handler = logging.FileHandler(self.test_results_dir / f"{self.test_name}.log")
        file_handler.setLevel(logging.DEBUG)
        file_handler.setFormatter(Formatter())
        self.logger.addHandler(file_handler)

    def test_fail(self, msg: str):
        self.logger.info(f"[{Color.FAIL}FAIL{Color.ENDC}] {self.test_name}: {msg}")
        self.status = False

    def test_pass(self):
        self.logger.info(f"[{Color.PASS}PASS{Color.ENDC}] {self.test_name}")

    def run(self, program: Path, options: list[str], copyback: bool):
        os.chdir(WORK_DIR)
        self.logger.info("duck")

        proc = subprocess.run(
            ["python3", str(program), str(self.test_path),
            "--output", str(self.test_results_dir)] + options, capture_output=True
        )

        if proc.stdout != b"":
            with open(self.test_results_dir / "stdout", "wb") as f:
                f.write(proc.stdout)

        if proc.stderr != b"":
            with open(self.test_results_dir / "stderr", "wb") as f:
                f.write(proc.stderr)

        if proc.returncode != 0:
            self.test_fail(f"{program} returned with code {proc.returncode}")
            return

        if self.status:
            self.test_pass()

        if copyback:
            # copy source/temp files into results directory
            pass

        for f in glob(f"./*"):
            p = Path(f)
            if p.is_dir():
                shutil.rmtree(p)
            else:
                os.remove(f)

        os.chdir(TEST_DIR)


class TestSuite():

    def __init__(self, name: str, config: dict, top_results_dir: Path) -> None:
        """Initialize TestSuite by cleaning directories and loading TOML data."""
        self.status: bool = True
        self.suite_name: str = name
        self.config: dict = config
        self.tests: list[TestCase] = []
        self.options: list[str] = []
        self.top_results_dir: Path = top_results_dir
        self.suite_results_dir: Path = top_results_dir / name
        self.pass_path = self.top_results_dir / "pass.txt"
        self.fail_path = self.top_results_dir / "fail.txt"

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
        self.status = False

    def suite_fail(self):
        self.logger.info(f"Suite {self.suite_name} finished with status {Color.BOLD}{Color.FAIL}FAIL{Color.ENDC}")
        self.status = False

    def suite_pass(self):
        self.logger.info(f"Suite {self.suite_name} finished with status {Color.BOLD}{Color.PASS}PASS{Color.ENDC}")

    def configure_tests(self):
        self.options.append(self.config["target"])

        test_file_dir = TEST_DIR / str(self.config["dir"])
        if not test_file_dir.is_dir():
            self.suite_fail_msg(f"File directory `{test_file_dir}` not a directory")

        for test_filename in [f for f in test_file_dir.glob("**/*") if f.is_file()]:
            test_path = test_file_dir / test_filename
            self.tests.append(TestCase(
                self.suite_name, 
                test_path.stem, 
                test_path, 
                self.top_results_dir
            ))

    def run(self, program: Path, copyback: bool):
        if not program.is_file():
            self.suite_fail_msg(f"`{program}` is not a file.")
            return

        if not self.status:
            return

        with open(self.pass_path, "w") as pass_file:
            with open(self.fail_path, "w") as fail_file:
                for test in self.tests:
                    test.run(program, self.options, copyback)
                    
                    if test.status:
                        pass_file.write(test.test_name + "\n")
                    else:
                        fail_file.write(test.test_name + "\n")

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
        print(suite_name)
        suites.append(TestSuite(suite_name, SUITE_NAME_MAP[suite_name], results_dir.absolute()))

    for suite in suites:
        suite.run(program, copyback)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("suites", nargs="+", choices=SUITE_NAMES,
                        help="names of test suites to run")
    parser.add_argument("--resultsdir", default=str(TEST_DIR / "resultsdir"),
                        help="directory to output test logs and copyback data")
    parser.add_argument("--translate", default=str(TEST_DIR / ".." / "translate.py"),
                        help="path to translate.py")
    parser.add_argument("--copyback", action="store_true",
                        help="copy all source, compiled, and log files from each testcase")
    args = parser.parse_args()

    main(Path(args.translate), Path(args.resultsdir), args.suites, args.copyback)
