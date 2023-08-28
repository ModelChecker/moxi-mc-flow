import argparse
from pathlib import Path
import sys

from il2btor.il2btor import translate


def main(src_filename: str, target_lang: str, use_json: bool) -> int:
    source_path = Path(src_filename)

    if not source_path.is_file():
        sys.stderr.write(f"Error: source is not a file ({source_path})")
        return 1

    with open(source_path, "r") as f:
        source = f.read()

    src_lang = ""
    if source_path.suffix == ".smv":
        src_lang = "smv"
    elif source_path.suffix == ".mcil":
        src_lang = "il"
    elif source_path.suffix == ".json":
        # assuming JSON files are IL representations
        src_lang = "il"
    else:
        sys.stderr.write(f"Error: file type unsupported ({source_path.suffix})")
        return 1

    # if src_lang == "il" and target_lang == "il"

    return 0


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("source",
                        help="source program to translate, language is inferred from file extension")
    parser.add_argument("target", choices=["il", "btor2"],
                        help="target language")
    parser.add_argument("--use-json", action="store_true",
                        help="use json as interchange format between translators")
    args = parser.parse_args()

    returncode = main(args.source, args.target, args.use_json)
    sys.exit(returncode)