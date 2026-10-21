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

# MoXI/SMT-LIB command names plus theory operators and sorts. User identifiers
# that match these cannot be declared in moxisc (e.g. a variable named `ite`).
MOXI_RESERVED_IDENTIFIERS = _RESERVED_SYMBOLS | frozenset(
    {
        "define-system",
        "check-system",
        "declare-sort",
        "declare-enum-sort",
        "declare-const",
        "define-const",
        "declare-fun",
        "define-sort",
        "define-fun",
        "set-logic",
        "exit",
        "Bool",
        "true",
        "false",
        "not",
        "=>",
        "and",
        "or",
        "xor",
        "=",
        "distinct",
        "ite",
        "const",
        "OnlyChange",
        "Array",
        "select",
        "store",
        "Int",
        "Real",
        "-",
        "+",
        "*",
        "div",
        "/",
        "<=",
        "<",
        ">=",
        ">",
        "divisible",
        "mod",
        "abs",
        "to_real",
        "to_int",
        "is_int",
        "BitVec",
        "concat",
        "extract",
        "repeat",
        "bvcomp",
        "bvredand",
        "bvredor",
        "bvnot",
        "bvand",
        "bvor",
        "bvnand",
        "bvnor",
        "bvxor",
        "bvxnor",
        "bvneg",
        "bvadd",
        "bvsub",
        "bvmul",
        "bvudiv",
        "bvurem",
        "bvsdiv",
        "bvsrem",
        "bvsmod",
        "bvshl",
        "bvlshr",
        "bvashr",
        "zero_extend",
        "sign_extend",
        "rotate_left",
        "rotate_right",
        "bvult",
        "bvule",
        "bvugt",
        "bvuge",
        "bvslt",
        "bvsle",
        "bvsgt",
        "bvsge",
    }
)


def is_reserved_moxi_ident(ident: str) -> bool:
    return ident in MOXI_RESERVED_IDENTIFIERS


def sanitize_moxi_ident(ident: str, occupied: set[str] | None = None) -> str:
    """Return `ident` unchanged, or a `_`-prefixed variant if it is reserved.

    `occupied` is the set of identifiers already in use; new names are added to
    it when a reserved identifier is rewritten.
    """
    if ident not in MOXI_RESERVED_IDENTIFIERS:
        return ident

    candidate = f"_{ident}"
    while candidate in MOXI_RESERVED_IDENTIFIERS or (
        occupied is not None and candidate in occupied
    ):
        candidate = f"_{candidate}"

    if occupied is not None:
        occupied.add(candidate)

    return candidate


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
