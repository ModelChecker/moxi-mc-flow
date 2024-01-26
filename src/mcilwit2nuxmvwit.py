from pathlib import Path
import pickle

from src import log, mcil_witness, nuxmv_witness, mcil, nuxmv

FILE_NAME = Path(__file__).name


def to_xmv_word_const(mcil_bitvec: mcil.MCILConstant) -> nuxmv.XMVWordConstant:
    width = mcil_bitvec.sort.identifier.indices[0]
    value = int(mcil_bitvec.value)
    return nuxmv.XMVWordConstant(f"0ud{width}_{value}")


def to_xmv_expr(mcil_expr: mcil.MCILExpr, symbol: str) -> nuxmv.XMVExpr:
    if isinstance(mcil_expr, mcil.MCILConstant) and mcil.is_bool_sort(mcil_expr.sort):
        return nuxmv.XMVBooleanConstant(mcil_expr.value)
    elif isinstance(mcil_expr, mcil.MCILConstant) and mcil.is_bitvec_sort(mcil_expr.sort):
        return to_xmv_word_const(mcil_expr)
    elif isinstance(mcil_expr, mcil.MCILApply) and mcil_expr.identifier.check({"const"}, 0):
        array_var = nuxmv.XMVIdentifier(nuxmv_witness.post_process_xmv_identifier(symbol))
        typeof = nuxmv.XMVFunCall("typeof", [array_var])
        value = to_xmv_expr(mcil_expr.children[0], symbol)
        return nuxmv.XMVFunCall("CONSTARRAY", [typeof, value])
    elif isinstance(mcil_expr, mcil.MCILApply) and mcil_expr.identifier.check({"store"}, 0):
        array,index,element = mcil_expr.children
        return nuxmv.XMVFunCall("WRITE", [
            to_xmv_expr(array, symbol), to_xmv_expr(index, symbol), to_xmv_expr(element, symbol)
        ])
    raise ValueError(f"{mcil_expr}")

def to_xmv_assign(mcil_assign: mcil_witness.MCILAssignment) -> nuxmv_witness.XMVAssignment:
    return nuxmv_witness.XMVAssignment(mcil_assign.symbol, to_xmv_expr(mcil_assign.value, mcil_assign.symbol))


def to_xmv_state(trace_id: int, mcil_state: mcil_witness.MCILState) -> nuxmv_witness.XMVState:
    return nuxmv_witness.XMVState(
        trace_id, mcil_state.index+1,
        [to_xmv_assign(a) for a in mcil_state.state_assigns],
        [to_xmv_assign(a) for a in mcil_state.input_assigns],
    )


def to_xmv_trail(
    trace_id: int, mcil_trace: mcil_witness.MCILTrail
) -> nuxmv_witness.XMVTrail:
    return nuxmv_witness.XMVTrail(
        [to_xmv_state(trace_id, s) for s in mcil_trace.states]
    )


def translate(
    mcil_response: mcil_witness.MCILQueryResponse,
    trace_id: int
) -> nuxmv_witness.XMVSpecResponse:
    if mcil_response.result is mcil_witness.MCILQueryResult.UNKNOWN:
        xmv_response = nuxmv_witness.XMVSpecResponse(
            nuxmv_witness.XMVSpecResult.UNKNOWN, mcil_response.symbol, None
        )
    elif mcil_response.result is mcil_witness.MCILQueryResult.UNSAT:
        xmv_response = nuxmv_witness.XMVSpecResponse(
            nuxmv_witness.XMVSpecResult.UNSAT, mcil_response.symbol, None
        )
    elif mcil_response.result is mcil_witness.MCILQueryResult.SAT:
        if not mcil_response.trace:
            raise ValueError

        xmv_trace = nuxmv_witness.XMVTrace(
            to_xmv_trail(trace_id, mcil_response.trace.prefix),
            to_xmv_trail(trace_id, mcil_response.trace.lasso) 
                if mcil_response.trace.lasso else None 
        )
        xmv_response = nuxmv_witness.XMVSpecResponse(
            nuxmv_witness.XMVSpecResult.SAT, mcil_response.symbol, xmv_trace
        )
    else:
        raise ValueError

    return xmv_response        


def main(
    input_path: Path, 
    output_path: Path,
    overwrite: bool
) -> int:
    xmv_responses: list[nuxmv_witness.XMVSpecResponse] = []    

    with open(str(input_path), "rb") as f:
        mcil_wit: mcil_witness.MCILWitness = pickle.load(f)

    if len(mcil_wit.responses) < 1:
        output_path.touch()
        return 0
    elif len(mcil_wit.responses) > 1:
        log.warning("mcil.MCIL witness should only have 1 check-system response, using first.", FILE_NAME)

    check_system_response = mcil_wit.responses[0]

    xmv_responses = [
        translate(query, id) 
        for query,id
        in zip(
            check_system_response.query_responses, 
            range(1,len(check_system_response.query_responses)+1)
        )
    ]

    xmv_witness = nuxmv_witness.XMVWitness(xmv_responses)

    if not overwrite and output_path.exists():
        log.error(f"Already exists: {output_path}\n\t"
                  "Did you mean to enable the '--overwrite' option?", FILE_NAME)
        return 1

    with open(str(output_path), "w") as f:
        f.write(str(xmv_witness))

    return 0
