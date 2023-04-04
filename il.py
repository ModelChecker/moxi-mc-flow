

class ILSystem():

    def __init__(self, attr: dict[str, str]) -> None:
        if "input" in attr:
            self.input = attr["input"]
        
        if "state" in attr:
            self.state = attr["state"]

        if "output" in attr:
            self.output = attr["output"]

        if "init" in attr:
            self.init = attr["init"]

        if "trans" in attr:
            self.trans = attr["trans"]
        
        if "inv" in attr:
            self.inv = attr["inv"]