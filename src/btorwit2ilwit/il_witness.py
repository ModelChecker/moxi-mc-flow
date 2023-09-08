from enum import Enum
from typing import Optional, Any


class ILQueryResult(Enum):
    UNKNOWN = "unknown"
    SAT = "sat"
    UNSAT = "unsat"


class ILCertificate():

    def __init__(self, symbol: str) -> None:
        self.symbol = symbol
        # TODO


class ILModel():

    def __init__(self, symbol: str) -> None:
        self.symbol = symbol
        # TODO


class ILState():

    def __init__(self, index: int, assignments: dict[str, Any]) -> None:
        self.index = index
        self.assignments = assignments

    def __str__(self) -> str:
        return "state"


class ILTrail():

    def __init__(self, symbol: str, states: list[ILState]) -> None:
        self.symbol = symbol
        self.states = states

    def __str__(self) -> str:
        return f"({self.symbol} " + "\n".join([str(s) for s in self.states]) + ")"


class ILTrace():

    def __init__(self, symbol: str, prefix: ILTrail, lasso: ILTrail) -> None:
        self.symbol = symbol
        self.prefix = prefix
        self.lasso = lasso

    def __str__(self) -> str:
        s = f"({self.symbol} :prefix {self.prefix.symbol}"
        if self.lasso:
            s += f" :lasso {self.lasso.symbol}"
        return s + ")"


class ILQueryResponse():

    def __init__(
            self, 
            symbol: str, 
            result: ILQueryResult, 
            model: Optional[ILModel], 
            trace: Optional[ILTrace],
            certificate: Optional[ILCertificate]
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


class ILCheckSystemResponse():

    def __init__(self, query_reponses: list[ILQueryResponse]):
        self.query_responses = query_reponses

        self.certificates = []
        self.models = []
        self.traces = []
        self.trails = []
        for response in query_reponses:
            self.certificates.append(response.certificate)
            self.models.append(response.model)
            self.traces.append(response.trace)

    def __str__(self) -> str:
        s = "(check-system-reponse \n"
        s += "\n".join([f":query {q}" for q in self.query_responses]) + "\n"
        s += "\n".join([f":trace {t}" for t in self.traces]) + "\n"
        s += "\n".join([f":trail {t}" for t in self.trails]) + "\n"
        s += "\n".join([f":model {m}" for m in self.models]) + "\n"
        s += "\n".join([f":certificate {c}" for c in self.certificates]) + "\n"
        return s + ")"


 