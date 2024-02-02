class BitVec:
    def __init__(self, width: int, value: int) -> None:
        self.width = width
        self.value = value

    def __str__(self) -> str:
        return "{0:0{w}b}".format(self.value, w=self.width)

    def __eq__(self, __o: object) -> bool:
        return (
            isinstance(__o, BitVec)
            and __o.value == self.value
            and __o.width == self.width
        )
