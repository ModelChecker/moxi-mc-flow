import sys
import os
import shutil
import inspect
from pathlib import Path

FILE_NAME = Path(__file__).name

def get_line_info() -> str:
    return f"{inspect.stack()[1][1]}:{inspect.stack()[1][2]}"

def eprint(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)

def rmdir(dir: Path, quiet: bool):
    """Remove `dir`, print a warning if quiet is False"""
    if dir.is_file():
        if not quiet:
            print(f"[{FILE_NAME}] Overwriting {dir}")
        os.remove(dir)
    elif dir.is_dir():
        if not quiet:
            print(f"[{FILE_NAME}] Overwriting {dir}")
        shutil.rmtree(dir)

def cleandir(dir: Path, quiet: bool):
    """Remove and create fresh `dir`, print a warning if quiet is False"""
    rmdir(dir, quiet)
    os.mkdir(dir)