import argparse
from enum import Enum
from pathlib import Path
import subprocess
import sys

# from smv2il.smv2json import main as smv2json
# from il2btor.json2il import main as json2il
# from il2btor.il2json import main as il2json
# from il2btor.il2btor import main as il2btor

CUR_DIR = Path(__file__).parent
SMV2MCIL_DIR = CUR_DIR / "smv2mcil"
MCIL2BTOR_DIR = CUR_DIR / "mcil2btor"

SMV2JSON = SMV2MCIL_DIR / "smv2json.py"
JSON2MCIL = MCIL2BTOR_DIR / "json2mcil.py"
MCIL2JSON = MCIL2BTOR_DIR / "mcil2json.py"
MCIL2BTOR = MCIL2BTOR_DIR / "mcil2btor.py"

class Lang(Enum):
    NONE = 0
    SMV = 1
    IL = 2
    IL_JSON = 3
    BTOR2 = 4


def main(src_path: Path, target_lang: Lang, target_path: Path, do_sort_check: bool) -> int:
    if not src_path.is_file():
        sys.stderr.write(f"Error: source is not a file ({src_path})\n")
        return 1

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
            # SMV -> json
            proc = subprocess.run(["python3", SMV2JSON, src_path, "--output", target_path])
            return proc.returncode
        elif target_lang == Lang.IL:
            # SMV -> IL
            json_path = Path(f"{target_path.stem}.json")
            proc = subprocess.run(["python3", SMV2JSON, src_path, "--output", json_path])
            if proc.returncode:
                return proc.returncode
            proc = subprocess.run(["python3", JSON2MCIL, json_path, "--output", target_path])
            return proc.returncode
        elif target_lang == Lang.BTOR2:
            # SMV -> BTOR2
            json_path = Path(f"{target_path.stem}.json")
            proc = subprocess.run(["python3", SMV2JSON, src_path, "--output", json_path])
            if proc.returncode:
                return proc.returncode
            proc = subprocess.run(["python3", MCIL2BTOR, json_path, "--output", target_path])
            return proc.returncode
    elif src_lang == Lang.IL:
        if target_lang == Lang.IL_JSON:
            # IL -> json
            proc = subprocess.run(["python3", MCIL2JSON, src_path, "--output", target_path])
            return proc.returncode
        elif target_lang == Lang.BTOR2:
            # IL -> BTOR2
            proc = subprocess.run(["python3", MCIL2BTOR, src_path, "--output", target_path])
            return proc.returncode
    elif src_lang == Lang.IL_JSON:
        if target_lang == Lang.IL:
            # json -> IL
            proc = subprocess.run(["python3", JSON2MCIL, src_path, "--output", target_path])
            return proc.returncode
        elif target_lang == Lang.BTOR2:
            # json -> BTOR2
            proc = subprocess.run(["python3", MCIL2BTOR, src_path, "--output", target_path])
            return proc.returncode

    return 0


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("source", help="source program to translate, language is inferred from file extension")
    parser.add_argument("targetlang", choices=["mcil", "mcil-json", "btor2"],
                        help="target language")
    parser.add_argument("--targetloc", help="target location; should be a directory if targetlang is 'btor2', a filename otherwise")
    parser.add_argument("--sortcheck", action="store_true",
                        help="enable sort checking if translating to il")
    args = parser.parse_args()

    src_path = Path(args.source)

    if args.targetlang == "mcil":
        target_lang = Lang.IL
        target_path = Path(args.targetloc) if args.targetloc else Path(f"{src_path.stem}.mcil")
    elif args.targetlang == "mcil-json":
        target_lang = Lang.IL_JSON
        target_path = Path(args.targetloc) if args.targetloc else Path(f"{src_path.stem}.json")
    elif args.targetlang == "btor2":
        target_lang = Lang.BTOR2
        if not args.targetloc:
            sys.stderr.write("Error: option 'targetloc' required for 'btor2' target\n")
            sys.exit(1)
        target_path = Path(args.targetloc)
    else:
        target_lang = Lang.NONE
        target_path = Path("")

    returncode = main(src_path, target_lang, target_path, args.sortcheck)
    sys.exit(returncode)