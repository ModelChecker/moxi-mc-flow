from enum import Enum
from typing import Optional

from src import moxi


class QueryResult(Enum):
    UNKNOWN = "unknown"
    SAT = "sat"
    UNSAT = "unsat"


class Certificate:
    def __init__(self, symbol: str) -> None:
        self.symbol = symbol
        # TODO


class Model:
    def __init__(self, symbol: str) -> None:
        self.symbol = symbol
        # TODO


class Assignment:
    def __init__(self, symbol: str, value: moxi.Term) -> None:
        self.symbol = symbol
        self.value = value

    def __str__(self) -> str:
        return f"({self.symbol} {str(self.value)})"


class State:
    def __init__(
        self,
        index: int,
        state_assigns: list[Assignment],
        input_assigns: list[Assignment],
    ) -> None:
        self.index = index
        self.state_assigns = state_assigns
        self.input_assigns = input_assigns
        self.assigns = state_assigns + input_assigns

    def __str__(self) -> str:
        assigns_str = " ".join([str(a) for a in self.assigns])
        return f"({self.index} {assigns_str})"


class Trail:
    def __init__(self, symbol: str, states: list[State]) -> None:
        self.symbol = symbol
        self.states = states

    def __str__(self) -> str:
        return f"({self.symbol} \n\t" + "\n\t".join([str(s) for s in self.states]) + ")"


class Trace:
    def __init__(self, symbol: str, prefix: Trail, lasso: Optional[Trail]) -> None:
        self.symbol = symbol
        self.prefix = prefix
        self.lasso = lasso

    def __str__(self) -> str:
        s = f"({self.symbol} :prefix {self.prefix.symbol}"
        if self.lasso:
            s += f" :lasso {self.lasso.symbol}"
        return s + ")"


class QueryResponse:
    def __init__(
        self,
        symbol: str,
        result: QueryResult,
        model: Optional[Model],
        trace: Optional[Trace],
        certificate: Optional[Certificate],
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


class CheckSystemResponse:
    def __init__(self, symbol: str, query_responses: list[QueryResponse]):
        self.symbol = symbol
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
        s = f"(check-system-response {self.symbol}\n"
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


class Witness:
    def __init__(self, responses: list[CheckSystemResponse]) -> None:
        self.responses = responses

    def __str__(self) -> str:
        return "\n\n".join([str(r) for r in self.responses])
