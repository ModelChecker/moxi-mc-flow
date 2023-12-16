from typing import Optional, cast

from .bitvec import BitVec

class BtorAssignment():

    def __init__(self, id: int, symbol: Optional[str]) -> None:
        self.id = id
        self.symbol = "" # TODO
        # self.symbol = symbol if symbol else ""


class BtorBitVecAssignment(BtorAssignment):

    def __init__(self, id: int, value: BitVec, symbol: Optional[str]) -> None:
        super().__init__(id, symbol)
        self.value = value
    
    def __str__(self) -> str:
        value = cast(int, self.value)
        return f"{self.id} {value} {self.symbol}"
        

class BtorArrayAssignment(BtorAssignment):

    def __init__(self, id: int, value: tuple[BitVec, BitVec], symbol: Optional[str]) -> None:
        super().__init__(id, symbol)
        (index, element) = value
        self.index = index
        self.element = element
    
    def __str__(self) -> str:
        return f"{self.id} [{self.index}] {self.element} {self.symbol}"


class BtorFrame():

    def __init__(
        self, 
        index: int,
        state_assigns: list[BtorAssignment], # TODO: make this a dict
        input_assigns: list[BtorAssignment]  # TODO: make this a dict
    ) -> None:
        self.index = index
        self.state_assigns = state_assigns
        self.input_assigns = input_assigns

    def __str__(self) -> str:
        s = f"#{self.index}\n" if self.state_assigns else f"#{self.index}"
        s += "\n".join([str(a) for a in self.state_assigns]) + "\n"
        s += f"@{self.index}\n" if self.input_assigns else f"@{self.index}"
        s += "\n".join([str(a) for a in self.input_assigns])
        return s


class BtorWitness():

    def __init__(
        self, 
        bad_props: list[int], 
        justice_props: list[int], 
        frames: list[BtorFrame]
    ) -> None:
        self.bad_props = bad_props
        self.justice_props = justice_props
        self.frames = frames

    def __str__(self) -> str:
        s = "sat\n"
        s += " ".join([f"b{p}" for p in self.bad_props] + [f"j{p}" for p in self.justice_props]) + "\n"
        s += "\n".join([str(f) for f in self.frames])
        return s
        