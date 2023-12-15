import argparse
from pathlib import Path
import sys
import os
import shutil

from src.util import eprint
from src.nuxmv2mcil import main as nuxmv2mcil
from src.mcil2btor import main as mcil2btor
from src.mcil2json import main as mcil2json
from src.json2mcil import main as json2mcil

sys.setrecursionlimit(10000)

FILE_NAME = Path(__file__).name
FILE_DIR = Path(__file__).parent
SMV2MCIL_DIR = FILE_DIR / "smv2mcil"
MCIL2BTOR_DIR = FILE_DIR / "mcil2btor"

SMV2JSON = SMV2MCIL_DIR / "smv2json.py"
JSON2MCIL = MCIL2BTOR_DIR / "json2mcil.py"
MCIL2JSON = MCIL2BTOR_DIR / "mcil2json.py"
MCIL2BTOR = MCIL2BTOR_DIR / "mcil2btor.py"


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


def main(input_path: Path, target_lang: str, output_path: Path) -> int:
    if not input_path.is_file():
        eprint(f"[{FILE_NAME}] source is not a file ({input_path})\n")
        return 1

    match (input_path.suffix, target_lang):
        case (".smv", "mcil"):
            return nuxmv2mcil(input_path, output_path, True)
        case (".smv", "mcil-json"):
            mcil_path = input_path.with_suffix(".mcil")
            retcode = nuxmv2mcil(input_path, mcil_path, True)
            if retcode:
                return retcode
            retcode = mcil2json(mcil_path, output_path, False, False)
            mcil_path.unlink()
            return retcode
        case (".smv", "btor2"):
            mcil_path = input_path.with_suffix(".mcil")
            retcode = nuxmv2mcil(input_path, mcil_path, True)
            if retcode:
                return retcode
            retcode = mcil2btor(mcil_path, output_path, None)
            mcil_path.unlink()
            return retcode
        case (".mcil", "mcil-json"):
            return mcil2json(input_path, output_path, False, False)
        case(".mcil", "btor2"):
            return mcil2btor(input_path, output_path, None)
        case (".json", "mcil"):
            return json2mcil(input_path, output_path, False, False)
        case (".json", "btor2"):
            mcil_path = input_path.with_suffix(".mcil")
            retcode = json2mcil(input_path, output_path, False, False)
            if retcode:
                return retcode
            retcode = mcil2btor(input_path, output_path, None)
            mcil_path.unlink()
            return retcode
        case _:
            return 0


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("input", help="input program to translate, language is inferred from file extension")
    parser.add_argument("targetlang", choices=["mcil", "mcil-json", "btor2"],
                        help="target language")
    parser.add_argument("--output", help="target location; should be a directory if targetlang is 'btor2', a filename otherwise")
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

    returncode = main(input_path, args.targetlang, output_path)
    sys.exit(returncode)