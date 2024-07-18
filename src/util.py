import pathlib
import os

FILE_NAME = pathlib.Path(__file__).name

def mkdir(dir: pathlib.Path) -> bool:
    if not dir.exists():
        os.mkdir(dir)
        return True
    elif dir.is_dir():
        return True
    else:
        return False
