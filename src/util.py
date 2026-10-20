import pathlib
import os
import re

FILE_NAME = pathlib.Path(__file__).name

# SMT-LIB 2.6 simple symbols: letters, digits, and ~!@$%^&*_+=<>.?/-,
# not starting with a digit and not a reserved word. See section 3.1.
# `|abc|` and `abc` are the same symbol; quoted form is never a reserved word.
_SIMPLE_SYMBOL_RE = re.compile(
    r"[a-zA-Z~!@$%^&*_+=<>.?/-][0-9a-zA-Z~!@$%^&*_+=<>.?/-]*\Z"
)
_RESERVED_SYMBOLS = frozenset(
    {
        "BINARY",
        "DECIMAL",
        "HEXADECIMAL",
        "NUMERAL",
        "STRING",
        "_",
        "!",
        "as",
        "let",
        "exists",
        "forall",
        "match",
        "par",
    }
)


def unquote_symbol(token: str) -> str:
    """Strip SMT-LIB quotes so `|abc|` and `abc` are the same symbol.

    MoXI also allows a trailing prime outside the quotes (`|x|'`) or inside
    (`|x'|`). Both become `x'` here; callers may then peel off the prime.
    """
    if token.startswith("|"):
        if token.endswith("|'") and len(token) >= 3:
            return token[1:-2] + "'"
        if token.endswith("|") and len(token) >= 2:
            return token[1:-1]
    return token


def is_simple_symbol(symbol: str) -> bool:
    return bool(_SIMPLE_SYMBOL_RE.match(symbol)) and symbol not in _RESERVED_SYMBOLS


def format_symbol(symbol: str, primed: bool = False) -> str:
    """Print `symbol`, quoting it if it is not an SMT-LIB simple symbol."""
    if is_simple_symbol(symbol):
        return symbol + ("'" if primed else "")
    return f"|{symbol}|" + ("'" if primed else "")


def mkdir(dir: pathlib.Path) -> bool:
    if not dir.exists():
        os.mkdir(dir)
        return True
    elif dir.is_dir():
        return True
    else:
        return False
