from pathlib import Path
import pickle

from .mcil_witness import *
from .nuxmv_witness import *
from .mcil import *
from .nuxmv import *
from .util import eprint

FILE_NAME = Path(__file__).name


def to_xmv_word_const(mcil_bitvec: MCILConstant) -> XMVWordConstant:
    width = mcil_bitvec.sort.identifier.indices[0]
    value = int(mcil_bitvec.value)
    return XMVWordConstant(f"0ud{width}_{value}")


def to_xmv_expr(mcil_expr: MCILExpr, symbol: str) -> XMVExpr:
    if isinstance(mcil_expr, MCILConstant) and is_bool_sort(mcil_expr.sort):
        return XMVBooleanConstant(mcil_expr.value)
    elif isinstance(mcil_expr, MCILConstant) and is_bitvec_sort(mcil_expr.sort):
        return to_xmv_word_const(mcil_expr)
    elif isinstance(mcil_expr, MCILApply) and mcil_expr.identifier.check({"const"}, 0):
        array_var = XMVIdentifier(post_process_xmv_identifier(symbol))
        typeof = XMVFunCall("typeof", [array_var])
        value = to_xmv_expr(mcil_expr.children[0], symbol)
        return XMVFunCall("CONSTARRAY", [typeof, value])
    elif isinstance(mcil_expr, MCILApply) and mcil_expr.identifier.check({"store"}, 0):
        array,index,element = mcil_expr.children
        return XMVFunCall("WRITE", [
            to_xmv_expr(array, symbol), to_xmv_expr(index, symbol), to_xmv_expr(element, symbol)
        ])
    raise ValueError(f"{mcil_expr}")

def to_xmv_assign(mcil_assign: MCILAssignment) -> XMVAssignment:
    return XMVAssignment(mcil_assign.symbol, to_xmv_expr(mcil_assign.value, mcil_assign.symbol))


def to_xmv_state(trace_id: int, mcil_state: MCILState) -> XMVState:
    return XMVState(
        trace_id, mcil_state.index+1,
        [to_xmv_assign(a) for a in mcil_state.state_assigns],
        [to_xmv_assign(a) for a in mcil_state.input_assigns],
    )


def to_xmv_trail(
    trace_id: int, mcil_trace: MCILTrail
) -> XMVTrail:
    return XMVTrail(
        [to_xmv_state(trace_id, s) for s in mcil_trace.states]
    )


def translate(
    mcil_response: MCILQueryResponse,
    trace_id: int
) -> XMVSpecResponse:
    if mcil_response.result is MCILQueryResult.UNKNOWN:
        xmv_response = XMVSpecResponse(
            XMVSpecResult.UNKNOWN, mcil_response.symbol, None
        )
    elif mcil_response.result is MCILQueryResult.UNSAT:
        xmv_response = XMVSpecResponse(
            XMVSpecResult.UNSAT, mcil_response.symbol, None
        )
    elif mcil_response.result is MCILQueryResult.SAT:
        if not mcil_response.trace:
            raise ValueError

        xmv_trace = XMVTrace(
            to_xmv_trail(trace_id, mcil_response.trace.prefix),
            to_xmv_trail(trace_id, mcil_response.trace.lasso) 
                if mcil_response.trace.lasso else None 
        )
        xmv_response = XMVSpecResponse(
            XMVSpecResult.SAT, mcil_response.symbol, xmv_trace
        )
    else:
        raise ValueError

    return xmv_response        


def main(
    input_path: Path, 
    output_path: Path
) -> int:
    xmv_responses: list[XMVSpecResponse] = []    

    with open(str(input_path), "rb") as f:
        mcil_witness: MCILWitness = pickle.load(f)

    if len(mcil_witness.responses) < 1:
        output_path.touch()
        return 0
    elif len(mcil_witness.responses) > 1:
        eprint(f"[{FILE_NAME}] Warning: MCIL witness should only have 1 check-system response, using first.")

    check_system_response = mcil_witness.responses[0]

    xmv_responses = [
        translate(query, id) 
        for query,id
        in zip(
            check_system_response.query_responses, 
            range(1,len(check_system_response.query_responses)+1)
        )
    ]

    xmv_witness = XMVWitness(xmv_responses)

    with open(str(output_path), "w") as f:
        f.write(str(xmv_witness))

    return 0
