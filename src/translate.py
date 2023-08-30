import argparse
from enum import Enum
from pathlib import Path
import sys

from il2btor.il2btor import main as il2btor
from smv2il.smv2il_json import main as smv2il_json


class Lang(Enum):
    SMV = 0
    IL = 1
    IL_JSON = 1
    BTOR2 = 2


def ext_to_lang(ext: str) -> Lang:
    match ext:
        case ".smv":
            return Lang.SMV
        case ".mcil":
            return Lang.IL
        case ".json":
            return Lang.IL_JSON
        case ".btor2":
            return Lang.BTOR2
        case _:
            raise NotImplementedError


def main(src_filename: str, target_lang: str) -> int:
    src_path = Path(src_filename)

    if not src_path.is_file():
        sys.stderr.write(f"Error: source is not a file ({src_path})")
        return 1

    with open(src_path, "r") as f:
        source = f.read()

    src_lang = ""
    if src_path.suffix == ".smv":
        src_lang = "smv"
    elif src_path.suffix == ".mcil":
        src_lang = "il"
    elif src_path.suffix == ".json":
        # assuming JSON files are IL representations
        src_lang = "il-json"
    else:
        sys.stderr.write(f"Error: file type unsupported ({src_path.suffix})")
        return 1

    if src_lang == target_lang:
        return 0
    elif src_lang == "smv":
        smv2il_json(src_filename, "tmp.json")

    
    elif src_lang == "il":
        il2btor(src_filename, "tmp.btor")
    

    return 0


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("src", help="source program to translate, language is inferred from file extension")
    parser.add_argument("target", choices=["il", "il-json", "btor2"],
                        help="target language")
    parser.add_argument("--target-filename", help="target filename")
    # parser.add_argument("--use-json", action="store_true",
    #                     help="use json as interchange format between translators")
    args = parser.parse_args()

    returncode = main(args.src, args.target)
    sys.exit(returncode)