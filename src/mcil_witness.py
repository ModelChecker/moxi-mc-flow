from enum import Enum
from typing import Optional, Any

from .bitvec import BitVec


class MCILQueryResult(Enum):
    UNKNOWN = "unknown"
    SAT = "sat"
    UNSAT = "unsat"


class MCILCertificate():

    def __init__(self, symbol: str) -> None:
        self.symbol = symbol
        # TODO


class MCILModel():

    def __init__(self, symbol: str) -> None:
        self.symbol = symbol
        # TODO


class MCILAssignment():

    def __init__(self, symbol: str) -> None:
        self.symbol = symbol


class MCILEnumAssignment(MCILAssignment):

    def __init__(self, symbol: str, value: str) -> None:
        super().__init__(symbol)
        self.value = value

    def __str__(self) -> str:
        return f"({self.symbol} {self.value})"


class MCILBitVecAssignment(MCILAssignment):

    def __init__(self, symbol: str, value: BitVec) -> None:
        super().__init__(symbol)
        self.value = value

    def __str__(self) -> str:
        return f"({self.symbol} #b{self.value})"


class MCILArrayAssignment(MCILAssignment):

    def __init__(self, symbol: str, value: tuple[BitVec, BitVec]) -> None:
        super().__init__(symbol)
        (index, element) = value
        self.index = index
        self.element = element

    def __str__(self) -> str:
        return f"({self.symbol} #b{self.index} #b{self.element})"


class MCILState():

    def __init__(self, index: int, assignments: list[MCILAssignment]) -> None:
        self.index = index
        self.assignments = assignments

    def __str__(self) -> str:
        assigns_str = " ".join([str(a) for a in self.assignments])
        return f"({self.index} {assigns_str})"


class MCILTrail():

    def __init__(self, symbol: str, states: list[MCILState]) -> None:
        self.symbol = symbol
        self.states = states

    def __str__(self) -> str:
        return f"({self.symbol} \n\t" + "\n\t".join([str(s) for s in self.states]) + ")"


class MCILTrace():

    def __init__(self, symbol: str, prefix: MCILTrail, lasso: Optional[MCILTrail]) -> None:
        self.symbol = symbol
        self.prefix = prefix
        self.lasso = lasso

    def __str__(self) -> str:
        s = f"({self.symbol} :prefix {self.prefix.symbol}"
        if self.lasso:
            s += f" :lasso {self.lasso.symbol}"
        return s + ")"


class MCILQueryResponse():

    def __init__(
            self, 
            symbol: str, 
            result: MCILQueryResult, 
            model: Optional[MCILModel], 
            trace: Optional[MCILTrace],
            certificate: Optional[MCILCertificate]
    ) -> None:
        self.symbol = symbol
        self.result = result
        self.model = model
        self.trace = trace
        self.certificate = certificate

    def __str__(self) -> str:
        s = f"({self.symbol} :result {self.result.value}"
        if self.model:
            s += f" :model {self.model.symbol}"
        if self.trace:
            s += f" :trace {self.trace.symbol}"
        if self.certificate:
            s += f" :certificate {self.certificate.symbol}"
        return s + ")"


class MCILCheckSystemResponse():

    def __init__(self, query_responses: list[MCILQueryResponse]):
        self.query_responses = query_responses

        self.certificates = []
        self.models = []
        self.traces = []
        self.trails = []
        for response in query_responses:
            if response.certificate:
                self.certificates.append(response.certificate)
            if response.model:
                self.models.append(response.model)
            if response.trace:
                self.traces.append(response.trace)
                if response.trace.prefix:
                    self.trails.append(response.trace.prefix)
                if response.trace.lasso:
                    self.trails.append(response.trace.lasso)

    def __str__(self) -> str:
        s = "(check-system-response \n"
        if self.query_responses:
            s += "\n".join([f":query {q}" for q in self.query_responses]) + "\n"
        if self.traces:
            s += "\n".join([f":trace {t}" for t in self.traces]) + "\n"
        if self.trails:
            s += "\n".join([f":trail {t}" for t in self.trails]) + "\n"
        if self.models:
            s += "\n".join([f":model {m}" for m in self.models]) + "\n"
        if self.certificates:
            s += "\n".join([f":certificate {c}" for c in self.certificates]) + "\n"
        return s + ")"


 