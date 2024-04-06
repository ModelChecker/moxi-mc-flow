import pathlib
import os
import shutil

from src import log

FILE_NAME = pathlib.Path(__file__).name


def rm(dir: pathlib.Path, quiet: bool):
    """Remove `dir`"""
    if dir.is_file():
        if not quiet:
            log.warning(f"Overwriting {dir}", FILE_NAME)
        os.remove(dir)
    elif dir.is_dir():
        if not quiet:
            log.warning(f"Overwriting {dir}", FILE_NAME)
        shutil.rmtree(dir)


def cleandir(dir: pathlib.Path, quiet: bool) -> None:
    """Remove and create fresh `dir`"""
    rm(dir, quiet)
    os.mkdir(dir)
