"""
Representation of VMT-LIB

Note: This enables C -> MoXI via Kratos2 (https://kratos.fbk.eu/)
"""

from __future__ import annotations
from pathlib import Path
from src import moxi

FILE_NAME = Path(__file__).name

class Program:
    def __init__(
        self,
        vars: list[tuple[str, moxi.Sort]],
        prev: dict[str, tuple[str, moxi.Sort]],
        next: dict[str, tuple[str, moxi.Sort]],
        init: list[moxi.Term],
        trans: list[moxi.Term],
        invar: dict[int, moxi.Term],
        live: dict[int, moxi.Term],
        funs: dict[str, moxi.Term]
    ):
        # If a var is in `vars` but not `prev`, then var is an input
        # Otherwise, var is an output
        self.vars: list[tuple[str, moxi.Sort]] = vars
        self.prev: dict[str, tuple[str, moxi.Sort]] = prev
        self.next: dict[str, tuple[str, moxi.Sort]] = next

        self.init_terms: list[moxi.Term] = init
        self.trans_terms: list[moxi.Term] = trans
        self.invar_properties: dict[int, moxi.Term] = invar
        self.live_properties: dict[int, moxi.Term] = live

        self.funs: dict[str, moxi.Term] = funs

