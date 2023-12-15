import argparse
import subprocess
from pathlib import Path
import shutil


FILE_NAME = Path(__file__).name
FILE_DIR = Path(__file__).parent

def run_and_copy(src: str, dst: str) -> str:
    print(src)
    return ""

def main(translate_path: Path, smvdir: Path, resultsdir: Path, ):
    if resultsdir.exists():
        shutil.rmtree(resultsdir)
    shutil.copytree(smvdir, resultsdir, copy_function=run_and_copy)

    for f in smvdir.glob("*.smv"):
        print(f)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("smvdir", help="directory of input SMV files")
    parser.add_argument("--resultsdir", default=f"{FILE_DIR.absolute()}/resultsdir",
                        help="directory to output test logs and copyback data")
    parser.add_argument("--copyback", action="store_true",
                        help="copy all source, compiled, and log files from each testcase")
    args = parser.parse_args()

    translate_path = FILE_DIR / "../translate.py"

    main(translate_path, Path(args.smvdir), Path(args.resultsdir))

