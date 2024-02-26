import argparse
import cProfile
import pathlib
import subprocess
import sys
from pstats import SortKey
from typing import Optional

from src import (
    btor,
    json2moxi,
    log,
    moxi2btor,
    moxi2json,
    parse_smv,
    smv2moxi,
)

FILE_NAME = pathlib.Path(__file__).name
FILE_DIR = pathlib.Path(__file__).parent
SMV2MCIL_DIR = FILE_DIR / "smv2moxi"
MCIL2BTOR_DIR = FILE_DIR / "moxi2btor"

CATBTOR = FILE_DIR / "btor2tools" / "build" / "bin" / "catbtor"
SORTCHECK = FILE_DIR / "sortcheck.py"

PASS = 0
FAIL = 1


def run_sortcheck(src_path: pathlib.Path) -> int:
    proc = subprocess.run(["python3", SORTCHECK, src_path], capture_output=True)

    if proc.returncode:
        log.error(proc.stderr.decode("utf-8"), FILE_NAME)
        return FAIL

    log.info(proc.stdout.decode("utf-8")[:-1], FILE_NAME)
    return PASS


def run_catbtor(src_path: pathlib.Path) -> int:
    proc = subprocess.run([CATBTOR, src_path], capture_output=True)

    if proc.returncode:
        log.error(proc.stderr.decode("utf-8"), FILE_NAME)
        return FAIL

    log.info(proc.stdout.decode("utf-8")[:-1], FILE_NAME)
    return PASS


def main(
    input_path: pathlib.Path,
    target_lang: str,
    output_path: pathlib.Path,
    keep: Optional[pathlib.Path],
    validate: bool,
    do_pickle: bool,
    do_cpp: bool,
    int_width: int,
) -> int:
    if not input_path.is_file():
        log.error(f"Source is not a file ({input_path})", FILE_NAME)
        return 1

    match (input_path.suffix, target_lang):
        case (".smv", "moxi"):
            if smv2moxi.translate_file(input_path, output_path, do_cpp):
                return FAIL
        case (".smv", "moxi-json"):
            moxi_path = input_path.with_suffix(".moxi")

            if smv2moxi.translate_file(input_path, moxi_path, do_cpp):
                return FAIL

            if moxi2json.main(moxi_path, output_path, False, False):
                return FAIL

            if keep:
                moxi_path.rename(keep)
            else:
                moxi_path.unlink()
        case (".smv", "btor2"):
            xmv_program = parse_smv.parse(input_path, do_cpp)
            if not xmv_program:
                log.error(f"Failed parsing specification in {input_path}", FILE_NAME)
                return 1

            moxi_program = smv2moxi.translate(input_path.name, xmv_program)
            if not moxi_program:
                log.error(
                    f"Failed translating specification in {input_path}", FILE_NAME
                )
                return 1

            btor2_program_set = moxi2btor.translate(moxi_program, int_width)

            if not btor2_program_set:
                return FAIL

            btor.write_btor2_program_set(
                btor2_program_set, output_path, do_pickle
            )

            if keep:
                with open(str(keep), "w") as f:
                    f.write(str(moxi_program))
        case (".moxi", "moxi-json"):
            if moxi2json.main(input_path, output_path, False, False):
                return FAIL
        case (".moxi", "btor2"):
            if moxi2btor.translate_file(
                input_path, output_path, int_width, do_pickle
            ):
                return FAIL
        case (".json", "moxi"):
            if json2moxi.main(input_path, output_path, False, False, int_width):
                return FAIL
        case (".json", "btor2"):
            moxi_path = input_path.with_suffix(".moxi")

            if json2moxi.main(input_path, moxi_path, False, False, int_width):
                return FAIL

            if moxi2btor.translate_file(
                moxi_path, output_path, int_width, do_pickle
            ):
                return FAIL

            if keep:
                moxi_path.rename(keep)
            else:
                moxi_path.unlink()
        case _:
            log.error(
                f"Translation unsupported: {input_path.suffix} to { target_lang}",
                FILE_NAME,
            )
            return 1

    if validate:
        if target_lang in {"moxi", "moxi-json"}:
            return run_sortcheck(output_path)
        elif target_lang in {"btor2"}:
            retcodes = [
                run_catbtor(btor_file) for btor_file in output_path.rglob("*.btor2")
            ]

            if any(retcodes):
                return 1
            
    return 0


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "input",
        help="input program to translate, language is inferred from file extension",
    )
    parser.add_argument(
        "targetlang", choices=["moxi", "moxi-json", "btor2"], help="target language"
    )
    parser.add_argument(
        "--output",
        help="target location; should be a directory if targetlang is 'btor2', a filename otherwise",
    )
    parser.add_argument("--keep", help="path to write intermediate translation file(s)")
    parser.add_argument(
        "--validate",
        action="store_true",
        help="validate output; uses catbtor if targetlan is btor2, sortcheck.py if targetlang is moxi or moxi-json",
    )
    parser.add_argument(
        "--pickle",
        action="store_true",
        help="if targetlang is `btor2`, dump pickled BTOR2; needed for witness translations",
    )
    parser.add_argument(
        "--cpp", action="store_true", help="runs cpp on input if input is SMV"
    )
    parser.add_argument("--catbtor", help="path to catbtor for BTOR2 validation")
    parser.add_argument("--sortcheck", help="path to sortcheck.py for MCIL validation")
    parser.add_argument(
        "--intwidth",
        default=32,
        type=int,
        help="bit width to translate Int types to when translating to BTOR2",
    )
    parser.add_argument("--debug", action="store_true", help="output debug messages")
    parser.add_argument("--quiet", action="store_true", help="disable output")
    parser.add_argument(
        "--profile", action="store_true", help="runs using cProfile if true"
    )

    args = parser.parse_args()

    if args.debug:
        log.set_debug()

    if args.quiet:
        log.set_quiet()

    input_path = pathlib.Path(args.input)

    if args.output:
        output_path = pathlib.Path(args.output)
    else:
        match args.targetlang:
            case "moxi":
                output_path = input_path.with_suffix(".moxi")
            case "moxi-json":
                output_path = input_path.with_suffix(".json")
            case "btor2":
                output_path = input_path.with_suffix("")
            case _:
                log.error("Invalid target language", FILE_NAME)
                sys.exit(1)

    if args.catbtor:
        CATBTOR = pathlib.Path(args.catbtor)

    if args.sortcheck:
        SORTCHECK = pathlib.Path(args.sortcheck)

    if args.profile:
        cProfile.run(
            "main(input_path, args.targetlang, output_path, args.keep, args.validate, args.pickle, args.cpp, args.intwidth)",
            sort=SortKey.TIME,
        )
        sys.exit(0)

    returncode = main(
        input_path,
        args.targetlang,
        output_path,
        args.keep,
        args.validate,
        args.pickle,
        args.cpp,
        args.intwidth,
    )
    sys.exit(returncode)
