import sys
import os
import shutil
from pathlib import Path
import logging

FILE_NAME = Path(__file__).name

class StandardFormatter(logging.Formatter):
    format_str = '%(levelname)s'

    FORMATS = {
        logging.DEBUG: '[%(filename)s:%(lineno)d] %(message)s',
        logging.INFO: '[%(module)s] %(message)s',
        logging.WARNING: '[%(filename)s:%(lineno)d] ' + format_str + ': %(message)s',
        logging.ERROR: '[%(filename)s:%(lineno)d] ' + format_str + ': %(message)s',
        logging.CRITICAL: '[%(filename)s:%(lineno)d] ' + format_str + ': %(message)s',
    }

    def format(self, record) -> str:
        log_fmt = self.FORMATS.get(record.levelno)
        formatter = logging.Formatter(log_fmt)
        return formatter.format(record)

LOGGER_NAME = __name__

logger = logging.getLogger(LOGGER_NAME)
logger.setLevel(logging.INFO)

stdout_handler = logging.StreamHandler(sys.stdout)
stdout_handler.setLevel(logging.DEBUG)
# filter out everything that is above INFO level (WARN, ERROR, ...)
stdout_handler.addFilter(lambda record: record.levelno <= logging.INFO)
stdout_handler.setFormatter(StandardFormatter())
logger.addHandler(stdout_handler)

stderr_handler = logging.StreamHandler(sys.stderr)
# take only warnings and error logs
stderr_handler.setLevel(logging.WARNING)
stderr_handler.setFormatter(StandardFormatter())
logger.addHandler(stderr_handler)


def rmdir(dir: Path, quiet: bool):
    """Remove `dir`, print a warning if quiet is False"""
    if dir.is_file():
        if not quiet:
            logger.info(f"Overwriting {dir}")
        os.remove(dir)
    elif dir.is_dir():
        if not quiet:
            logger.info(f"Overwriting {dir}")
        shutil.rmtree(dir)


def cleandir(dir: Path, quiet: bool):
    """Remove and create fresh `dir`, print a warning if quiet is False"""
    rmdir(dir, quiet)
    os.mkdir(dir)


def error(msg: str) -> bool:
    logger.error(msg)
    return False