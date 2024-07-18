"""Module for logging.

Error messaging (source file location) are inspired by GNU error message standards (https://www.gnu.org/prep/standards/standards.html#Errors).
"""
import enum
import sys
from typing import NamedTuple, Optional

debug_level = 0
enable_quiet = False


class FileLocation(NamedTuple):
    filename: str
    lineno: int


class Color(enum.Enum):
    HEADER = "\033[95m"
    OKBLUE = "\033[94m"
    OKCYAN = "\033[96m"
    OKGREEN = "\033[92m"
    WARN = "\033[93m"
    FAIL = "\033[91m"
    ENDC = "\033[0m"
    BOLD = "\033[1m"
    UNDERLINE = "\033[4m"


def set_debug_level(level: int) -> None:
    global debug_level
    debug_level = level


def set_quiet() -> None:
    global enable_quiet
    enable_quiet = True


def format(
    message: str,
    level: str,
    color: Optional[Color],
    module: str,
    location: Optional[FileLocation] = None,
) -> str:
    formatted_message = ""

    formatted_message += f"{module}:"

    if level == "INFO":
        pass
    elif color:
        formatted_message += f" {color.value}{level}{Color.ENDC.value}:"
    else:
        formatted_message += f" {level}:"

    if location:
        formatted_message += f" {location.filename}:{location.lineno}:"

    formatted_message += f" {message}\n"

    return formatted_message


def debug(
    level: int,
    message: str,
    module: str,
    location: Optional[FileLocation] = None,
) -> None:
    if level > debug_level or enable_quiet:
        return
    formatted_message = format(
        message, "DEBUG", Color.OKBLUE, module, location
    )
    sys.stderr.write(formatted_message)


def info(
    message: str,
    module: str,
    location: Optional[FileLocation] = None,
) -> None:
    if enable_quiet:
        return
    formatted_message = format(message, "INFO", None, module, location)
    sys.stderr.write(formatted_message)


def warning(
    message: str,
    module: str,
    location: Optional[FileLocation] = None,
) -> None:
    if enable_quiet:
        return
    formatted_message = format(message, "WARNING", Color.WARN, module, location)
    sys.stderr.write(formatted_message)


def error(
    message: str,
    module: str,
    location: Optional[FileLocation] = None,
) -> None:
    formatted_message = format(message, "ERROR", Color.FAIL, module, location)
    sys.stderr.write(formatted_message)


def internal(
    message: str,
    module: str,
    location: Optional[FileLocation] = None,
) -> None:
    formatted_message = format(message, "BUG", Color.FAIL, module, location)
    sys.stderr.write(formatted_message)
