import argparse
from enum import Enum
from pathlib import Path
import sys

from smv2il.smv2json import main as smv2json
from il2btor.json2il import main as json2il
from il2btor.il2json import main as il2json
from il2btor.il2btor import main as il2btor


class Lang(Enum):
    NONE = 0
    SMV = 1
    IL = 2
    IL_JSON = 3
    BTOR2 = 4


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


def main(src_path: Path, target_lang: Lang, target_path: Path, do_sort_check: bool) -> int:
    if not src_path.is_file():
        sys.stderr.write(f"Error: source is not a file ({src_path})\n")
        return 1

    with open(src_path, "r") as f:
        source = f.read()

    src_lang = ""
    if src_path.suffix == ".smv":
        src_lang = Lang.SMV
    elif src_path.suffix == ".mcil":
        src_lang = Lang.IL
    elif src_path.suffix == ".json":
        # assuming JSON files are IL representations
        src_lang = Lang.IL_JSON
    else:
        sys.stderr.write(f"Error: file type unsupported ({src_path.suffix})\n")
        return 1

    if src_lang == target_lang:
        return 0
    elif src_lang == Lang.SMV:
        if target_lang == Lang.IL_JSON:
            return smv2json(src_path, target_path)
        elif target_lang == Lang.IL:
            json_path = Path(f"{target_path.stem}.json")
            tmp = smv2json(src_path, json_path)
            if tmp:
                return tmp
            return json2il(json_path, target_path, do_sort_check)
        elif target_lang == Lang.BTOR2:
            json_path = Path(f"{target_path.stem}.json")
            tmp = smv2json(src_path, json_path)
            if tmp:
                return tmp
            return il2btor(json_path, target_path)
    elif src_lang == Lang.IL:
        if target_lang == Lang.IL_JSON:
            return il2json(src_path, target_path, do_sort_check, False)
        elif target_lang == Lang.BTOR2:
            return il2btor(src_path, target_path)
    elif src_lang == Lang.IL_JSON:
        if target_lang == Lang.IL:
            return json2il(src_path, target_path, do_sort_check)
        elif target_lang == Lang.BTOR2:
            return il2btor(src_path, target_path)

    return 0


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("source", help="source program to translate, language is inferred from file extension")
    parser.add_argument("targetlang", choices=["il", "il-json", "btor2"],
                        help="target language")
    parser.add_argument("--targetloc", help="target location; should be a directory if targetlang is 'btor2', a filename otherwise")
    parser.add_argument("--sortcheck", action="store_true",
                        help="enable sort checking if translating to il")
    args = parser.parse_args()

    src_path = Path(args.source)

    if args.targetlang == "il":
        target_lang = Lang.IL
        target_path = Path(args.targetloc) if args.targetloc else Path(f"{src_path.stem}.mcil")
    elif args.targetlang == "il-json":
        target_lang = Lang.IL_JSON
        target_path = Path(args.targetloc) if args.targetloc else Path(f"{src_path.stem}.json")
    elif args.targetlang == "btor2":
        target_lang = Lang.BTOR2
        if not args.targetloc:
            sys.stderr.write("Error: option 'targetloc' required for 'btor2' target")
            sys.exit(1)
        target_path = Path(args.targetloc)
    else:
        target_lang = Lang.NONE
        target_path = Path("")

    returncode = main(src_path, target_lang, target_path, args.sortcheck)
    sys.exit(returncode)