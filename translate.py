import argparse
import subprocess
from pathlib import Path
import sys
import os
import shutil

import cProfile

from src.util import eprint
from src.nuxmv2mcil import main as nuxmv2mcil
from src.mcil2btor import main as mcil2btor
from src.mcil2json import main as mcil2json
from src.json2mcil import main as json2mcil

FILE_NAME = Path(__file__).name
FILE_DIR = Path(__file__).parent
SMV2MCIL_DIR = FILE_DIR / "smv2mcil"
MCIL2BTOR_DIR = FILE_DIR / "mcil2btor"

CATBTOR = FILE_DIR / "btor2tools" / "build" / "bin" / "catbtor"
SORTCHECK = FILE_DIR / "sortcheck.py"

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


def main(input_path: Path, target_lang: str, output_path: Path, validate: bool, int_width: int) -> int:
    if not input_path.is_file():
        eprint(f"[{FILE_NAME}] source is not a file ({input_path})\n")
        return 1

    match (input_path.suffix, target_lang):
        case (".smv", "mcil"):
            retcode = nuxmv2mcil(input_path, output_path, True)
            if retcode:
                return retcode
        case (".smv", "mcil-json"):
            mcil_path = input_path.with_suffix(".mcil")

            retcode = nuxmv2mcil(input_path, mcil_path, True)
            if retcode:
                return retcode

            retcode = mcil2json(mcil_path, output_path, False, False)
            if retcode:
                return retcode

            mcil_path.unlink()
        case (".smv", "btor2"):
            mcil_path = input_path.with_suffix(".mcil")

            retcode = nuxmv2mcil(input_path, mcil_path, True)
            if retcode:
                return retcode

            retcode = mcil2btor(mcil_path, output_path, None, int_width)
            if retcode:
                return retcode

            mcil_path.unlink()
        case (".mcil", "mcil-json"):
            retcode = mcil2json(input_path, output_path, False, False)
            if retcode:
                return retcode
        case(".mcil", "btor2"):
            retcode = mcil2btor(input_path, output_path, None, int_width)
            if retcode:
                return retcode
        case (".json", "mcil"):
            retcode = json2mcil(input_path, output_path, False, False)
            if retcode:
                return retcode
        case (".json", "btor2"):
            mcil_path = input_path.with_suffix(".mcil")

            retcode = json2mcil(input_path, output_path, False, False)
            if retcode:
                return retcode

            retcode = mcil2btor(input_path, output_path, None, int_width)
            if retcode:
                return retcode

            mcil_path.unlink()
        case _:
            return 1

    if validate:
        if target_lang in {"mcil", "mcil-json"}:
            proc = subprocess.run(["python3", SORTCHECK, output_path])
            if proc.returncode:
                return proc.returncode
        elif target_lang in {"btor2"}:
            for btor_file in output_path.rglob("*"):
                proc = subprocess.run([CATBTOR, btor_file])
                if proc.returncode:
                    return proc.returncode

    return 0


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("input", help="input program to translate, language is inferred from file extension")
    parser.add_argument("targetlang", choices=["mcil", "mcil-json", "btor2"],
                        help="target language")
    parser.add_argument("--output", help="target location; should be a directory if targetlang is 'btor2', a filename otherwise")
    parser.add_argument("--validate", action="store_true", 
                        help="validate output; uses catbtor if targetlan is btor2, sortcheck.py if targetlang is mcil or mcil-json")
    parser.add_argument("--catbtor", help="path to catbtor for BTOR2 validation")
    parser.add_argument("--sortcheck", help="path to sortcheck.py for MCIL validation")
    parser.add_argument("--intwidth", default=32, type=int, help="bit width to translate Int types to when translating to BTOR2")
    args = parser.parse_args()

    input_path = Path(args.input)

    if args.output:
        output_path = Path(args.output) 
    else:
        match args.targetlang:
            case "mcil":
                output_path = input_path.with_suffix(".mcil")
            case "mcil-json":
                output_path = input_path.with_suffix(".json")
            case "btor2":
                output_path = input_path.with_suffix("")
                cleandir(output_path, False)
            case _:
                eprint(f"[{FILE_NAME}] invalid target language")
                sys.exit(1)

    if args.catbtor:
        CATBTOR = Path(args.catbtor)

    if args.sortcheck:
        SORTCHECK = Path(args.sortcheck)

    # cProfile.run("main(input_path, args.targetlang, output_path)")

    returncode = main(input_path, args.targetlang, output_path, args.validate, args.intwidth)
    sys.exit(returncode)