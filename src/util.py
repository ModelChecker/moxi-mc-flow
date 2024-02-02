import pathlib
import os
import shutil

from src import log

FILE_NAME = pathlib.Path(__file__).name


def rmdir(dir: pathlib.Path):
    """Remove `dir`"""
    if dir.is_file():
        log.warning(f"Overwriting {dir}", FILE_NAME)
        os.remove(dir)
    elif dir.is_dir():
        log.warning(f"Overwriting {dir}", FILE_NAME)
        shutil.rmtree(dir)


def cleandir(dir: pathlib.Path, overwrite: bool) -> bool:
    """Remove and create fresh `dir`"""
    if not overwrite and dir.exists():
        log.error(
            f"Already exists: {dir}\n\t"
            "Did you mean to enable the '--overwrite' option?",
            FILE_NAME,
        )
        return False

    rmdir(dir)
    os.mkdir(dir)

    return True
