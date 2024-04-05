import pathlib
import os
import shutil

from src import log

FILE_NAME = pathlib.Path(__file__).name


def rm(dir: pathlib.Path):
    """Remove `dir`"""
    if dir.is_file():
        log.warning(f"Overwriting {dir}", FILE_NAME)
        os.remove(dir)
    elif dir.is_dir():
        log.warning(f"Overwriting {dir}", FILE_NAME)
        shutil.rmtree(dir)


def cleandir(dir: pathlib.Path) -> None:
    """Remove and create fresh `dir`"""
    rm(dir)
    os.mkdir(dir)
