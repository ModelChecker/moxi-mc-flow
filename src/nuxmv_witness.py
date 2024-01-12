"""
Representation of nuXmv witnesses (mostly traces). See Section 4.7 (p97) of https://nuxmv.fbk.eu/downloads/nuxmv-user-manual.pdf for reference. 
"""
from enum import Enum
from typing import Optional

from .nuxmv import *


class XMVSpecResult(Enum):
    UNKNOWN = "unknown"
    SAT = "false"
    UNSAT = "true"


def post_process_xmv_identifier(xmv_identifier: str) -> str:
    # reverse the pre-processing steps from preprocess_nuxmv.py
    return (xmv_identifier.replace('_dot_', '.')
        .replace('_colon_', ':')
        .replace("_dquote_","\"")
        .replace('_dollar_','$')
        .replace('_lbrack_','[')
        .replace('_rbrack_',']',)
        .replace('_dbs_',r'\\'))


class XMVAssignment():

    def __init__(self, symbol: str, value: XMVExpr) -> None:
        self.symbol = post_process_xmv_identifier(symbol)
        self.value = value

    def __str__(self) -> str:
        return f"{self.symbol} = {self.value}"


class XMVState():

    def __init__(
        self, 
        trace_id: int, 
        index: int, 
        state_assigns: list[XMVAssignment],
        input_assigns: list[XMVAssignment]
    ) -> None:
        self.trace_id = trace_id
        self.index = index
        self.state_assigns = state_assigns
        self.input_assigns = input_assigns

    def __str__(self) -> str:
        s = ""

        # Input of first frame is omitted in nuXmv traces
        if self.input_assigns and self.index != 1:
            s += f"  -> Input: {self.trace_id}.{self.index} <-\n"
            for assign in self.input_assigns:
                s += f"    {assign}\n"

        if self.state_assigns:
            s += f"  -> State: {self.trace_id}.{self.index} <-\n"
            for assign in self.state_assigns:
                s += f"    {assign}\n"

        return s


class XMVTrail():

    def __init__(self, states: list[XMVState]) -> None:
        self.states = states

    def __str__(self) -> str:
        return "".join(str(state) for state in self.states)


class XMVTrace():

    def __init__(self, prefix: XMVTrail, lasso: Optional[XMVTrail]) -> None:
        self.prefix = prefix
        self.lasso = lasso

    def __str__(self) -> str:
        s =  "Trace Description: nuxmv2btor counterexample\n"
        s += "Trace Type: Counterexample\n"
        s += str(self.prefix)
        if self.lasso:
            s += f"  -- Loop starts here\n"
            s += str(self.lasso)
        return s[:-1] # remove trailing \n


class XMVSpecResponse():

    def __init__(self, result: XMVSpecResult, spec: str, trace: Optional[XMVTrace]) -> None:
        self.result = result
        self.spec = spec
        self.trace = trace

    def __str__(self) -> str:
        s = f"-- specification {self.spec} is {self.result.value}\n"
        if self.trace:
            s += f"-- as demonstrated by the following execution sequence\n"
            s += str(self.trace)
        return s


class XMVWitness():

    def __init__(
        self, 
        responses: list[XMVSpecResponse],
    ) -> None:
        self.responses = responses

    def __str__(self) -> str:
        return "\n".join(str(r) for r in self.responses)