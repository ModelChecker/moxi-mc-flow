from typing import Optional, cast


class BitVec():

    def __init__(self, width: int, value: int) -> None:
        self.width = width
        self.value = value

    def __str__(self) -> str:
        return "{0:0{w}b}".format(self.value, w=self.width)


class BtorAssignment():

    def __init__(self, id: int, value: int | tuple[int, int], symbol: Optional[str]) -> None:
        self.id = id
        self.value = value
        self.symbol = symbol


class BtorBitVecAssignment(BtorAssignment):

    def __init__(self, id: int, value: int, symbol: Optional[str]) -> None:
        super().__init__(id, value, symbol)
    
    def __str__(self) -> str:
        value = cast(int, self.value)
        return f"{self.id} {bin(value)} {self.symbol}"
        

class BtorArrayAssignment(BtorAssignment):

    def __init__(self, id: int, value: tuple[int, int], symbol: Optional[str]) -> None:
        super().__init__(id, value, symbol)
        (index, element) = value
        self.index = index
        self.element = element
    
    def __str__(self) -> str:
        return f"{self.id} [{bin(self.index)}] {bin(self.element)} {self.symbol}"


class BtorFrame():

    def __init__(
        self, 
        index: int,
        state_assigns: list[BtorAssignment],
        input_assigns: list[BtorAssignment]
    ) -> None:
        self.index = index
        self.state_assigns = state_assigns
        self.input_assigns = input_assigns

    def __str__(self) -> str:
        s = f"#{self.index}\n"
        s += "\n".join([str(a) for a in self.state_assigns])
        s += f"@{self.index}\n"
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
        