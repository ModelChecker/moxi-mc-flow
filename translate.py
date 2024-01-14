import argparse
import subprocess
from pathlib import Path
import sys
import logging

from src.util import cleandir, logger
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

PASS = 0
FAIL = 1

def run_sortcheck(src_path: Path) -> int:
    proc = subprocess.run(
        ["python3", SORTCHECK, src_path],
        capture_output=True
    )
    
    if proc.returncode:
        logger.error(proc.stderr.decode("utf-8"))
        return FAIL

    print(proc.stdout.decode("utf-8"))
    return PASS


def run_catbtor(src_path: Path) -> int:
    proc = subprocess.run(
        [CATBTOR, src_path], 
        capture_output=True
    )
    
    if proc.returncode:
        logger.error(proc.stderr.decode("utf-8"))
        return FAIL

    print(f"{src_path} is well-sorted")
    return PASS


def main(
    input_path: Path, 
    target_lang: str, 
    output_path: Path, 
    keep: bool,
    validate: bool,
    do_pickle: bool, 
    do_cpp: bool, 
    int_width: int,
) -> int:
    if not input_path.is_file():
        logger.error(f"source is not a file ({input_path})\n")
        return 1

    match (input_path.suffix, target_lang):
        case (".smv", "mcil"):
            if nuxmv2mcil(input_path, output_path, do_cpp):
                return FAIL
        case (".smv", "mcil-json"):
            mcil_path = input_path.with_suffix(".mcil")

            if nuxmv2mcil(input_path, mcil_path, do_cpp):
                return FAIL

            if mcil2json(mcil_path, output_path, False, False):
                return FAIL

            if not keep:
                mcil_path.unlink()
        case (".smv", "btor2"):
            mcil_path = input_path.with_suffix(".mcil")

            if  nuxmv2mcil(input_path, mcil_path, do_cpp):
                return FAIL

            if  mcil2btor(mcil_path, output_path, int_width, do_pickle):
                return FAIL

            if not keep:
                mcil_path.unlink()
        case (".mcil", "mcil-json"):
            if  mcil2json(input_path, output_path, False, False):
                return FAIL
        case(".mcil", "btor2"):
            if  mcil2btor(input_path, output_path, int_width, do_pickle):
                return FAIL
        case (".json", "mcil"):
            if  json2mcil(input_path, output_path, False, False, int_width):
                return FAIL
        case (".json", "btor2"):
            mcil_path = input_path.with_suffix(".mcil")

            if  json2mcil(input_path, mcil_path, False, False, int_width):
                return FAIL

            if  mcil2btor(mcil_path, output_path, int_width, do_pickle):
                return FAIL

            if not keep:
                mcil_path.unlink()
        case _:
            logger.error(f"Translation unsupported: {input_path.suffix} to { target_lang}")
            return 1

    if validate:
        if target_lang in {"mcil", "mcil-json"}:
            return run_sortcheck(output_path)
        elif target_lang in {"btor2"}:
            retcodes = [
                run_catbtor(btor_file) 
                for btor_file 
                in output_path.rglob("*.btor2")
            ]

            if any(retcodes):
                return 1

    return 0


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("input", help="input program to translate, language is inferred from file extension")
    parser.add_argument("targetlang", choices=["mcil", "mcil-json", "btor2"],
                        help="target language")
    parser.add_argument("--output", help="target location; should be a directory if targetlang is 'btor2', a filename otherwise")
    parser.add_argument("--keep", action="store_true", 
        help="keep intermediate translation files")
    parser.add_argument("--validate", action="store_true", 
                        help="validate output; uses catbtor if targetlan is btor2, sortcheck.py if targetlang is mcil or mcil-json")
    parser.add_argument("--pickle", action="store_true", 
                        help="if targetlang is `btor2`, dump pickled BTOR2; needed for witness translations")
    parser.add_argument("--cpp", action="store_true", 
                        help="runs cpp on input if input is SMV")
    parser.add_argument("--catbtor", help="path to catbtor for BTOR2 validation")
    parser.add_argument("--sortcheck", help="path to sortcheck.py for MCIL validation")
    parser.add_argument("--intwidth", default=32, type=int, help="bit width to translate Int types to when translating to BTOR2")
    parser.add_argument("--debug", action="store_true", 
                        help="output debug messages")
    args = parser.parse_args()

    if args.debug:
        logger.setLevel(logging.DEBUG)
    print("level")

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
                logger.error(f"invalid target language")
                sys.exit(1)

    if args.catbtor:
        CATBTOR = Path(args.catbtor)

    if args.sortcheck:
        SORTCHECK = Path(args.sortcheck)

    # cProfile.run("main(input_path, args.targetlang, output_path)")

    returncode = main(input_path, args.targetlang, output_path, args.keep, args.validate, args.pickle, args.cpp, args.intwidth)
    sys.exit(returncode)