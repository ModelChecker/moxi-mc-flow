from typing import Optional, cast


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
        assigns: list[BtorAssignment],
    ) -> None:
        self.assigns = assigns

    def __str__(self) -> str:
        return "\n".join([str(a) for a in self.assigns])


class BtorWitness():

    def __init__(
        self, 
        bad_props: list[int], 
        justice_props: list[int], 
        frames: list[tuple[BtorFrame, BtorFrame]]
    ) -> None:
        self.bad_props = bad_props
        self.justice_props = justice_props
        self.frames = frames
        self.state_frames, self.input_frames = list(zip(*frames))

    def __str__(self) -> str:
        s = "sat\n"
        s += " ".join([f"b{p}" for p in self.bad_props] + [f"j{p}" for p in self.justice_props]) + "\n"
        frame_idx = 0
        for frame in self.frames:
            state_frame, input_frame = frame
            s += f"#{frame_idx}\n"
            s += str(state_frame)
            s += f"@{frame_idx}\n"
            s += str(input_frame)
            frame_idx += 1
        return s
        