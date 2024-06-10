from pathlib import Path
import pickle

from src import log, moxi, moxi_witness, smv, smv_witness

FILE_NAME = Path(__file__).name


def to_xmv_word_const(moxi_bitvec: moxi.Constant) -> smv.WordConstant:
    width = moxi_bitvec.sort.identifier.indices[0]
    value = int(moxi_bitvec.value)
    return smv.WordConstant(f"0ud{width}_{value}")


def to_xmv_expr(moxi_expr: moxi.Term, symbol: str) -> smv.Expr:
    if isinstance(moxi_expr, moxi.Constant) and moxi.is_bool_sort(moxi_expr.sort):
        return smv.BooleanConstant(moxi_expr.value)
    elif isinstance(moxi_expr, moxi.Constant) and moxi.is_bitvec_sort(moxi_expr.sort):
        return to_xmv_word_const(moxi_expr)
    elif isinstance(moxi_expr, moxi.Apply) and moxi_expr.identifier.check({"const"}, 0):
        array_var = smv.Identifier(smv_witness.post_process_xmv_identifier(symbol))
        typeof = smv.FunCall("typeof", [array_var])
        value = to_xmv_expr(moxi_expr.children[0], symbol)
        return smv.FunCall("CONSTARRAY", [typeof, value])
    elif isinstance(moxi_expr, moxi.Apply) and moxi_expr.identifier.check({"store"}, 0):
        array, index, element = moxi_expr.children
        return smv.FunCall(
            "WRITE",
            [
                to_xmv_expr(array, symbol),
                to_xmv_expr(index, symbol),
                to_xmv_expr(element, symbol),
            ],
        )
    raise ValueError(f"{moxi_expr}")


def to_xmv_assign(moxi_assign: moxi_witness.Assignment) -> smv_witness.Assignment:
    return smv_witness.Assignment(
        moxi_assign.symbol, to_xmv_expr(moxi_assign.value, moxi_assign.symbol)
    )


def to_xmv_state(trace_id: int, moxi_state: moxi_witness.State) -> smv_witness.State:
    return smv_witness.State(
        trace_id,
        moxi_state.index + 1,
        [to_xmv_assign(a) for a in moxi_state.state_assigns],
        [to_xmv_assign(a) for a in moxi_state.input_assigns],
    )


def to_xmv_trail(trace_id: int, moxi_trace: moxi_witness.Trail) -> smv_witness.Trail:
    return smv_witness.Trail([to_xmv_state(trace_id, s) for s in moxi_trace.states])


def translate(
    moxi_response: moxi_witness.QueryResponse, trace_id: int
) -> smv_witness.SpecResponse:
    if moxi_response.result is moxi_witness.QueryResult.UNKNOWN:
        xmv_response = smv_witness.SpecResponse(
            smv_witness.SpecResult.UNKNOWN, moxi_response.symbol, None
        )
    elif moxi_response.result is moxi_witness.QueryResult.UNSAT:
        xmv_response = smv_witness.SpecResponse(
            smv_witness.SpecResult.UNSAT, moxi_response.symbol, None
        )
    elif moxi_response.result is moxi_witness.QueryResult.SAT:
        if not moxi_response.trace:
            raise ValueError

        xmv_trace = smv_witness.Trace(
            to_xmv_trail(trace_id, moxi_response.trace.prefix),
            to_xmv_trail(trace_id, moxi_response.trace.lasso)
            if moxi_response.trace.lasso
            else None,
        )
        xmv_response = smv_witness.SpecResponse(
            smv_witness.SpecResult.SAT, moxi_response.symbol, xmv_trace
        )
    else:
        raise ValueError

    return xmv_response


def main(input_path: Path, output_path: Path) -> int:
    xmv_responses: list[smv_witness.SpecResponse] = []

    with open(str(input_path), "rb") as f:
        moxi_wit: moxi_witness.Witness = pickle.load(f)

    if len(moxi_wit.responses) < 1:
        output_path.touch()
        return 0
    elif len(moxi_wit.responses) > 1:
        log.warning(
            "moxi. witness should only have 1 check-system response, using first.",
            FILE_NAME,
        )

    check_system_response = moxi_wit.responses[0]

    xmv_responses = [
        translate(query, id)
        for query, id in zip(
            check_system_response.query_responses,
            range(1, len(check_system_response.query_responses) + 1),
        )
    ]

    xmv_witness = smv_witness.Witness(xmv_responses)

    with open(str(output_path), "w") as f:
        f.write(str(xmv_witness))

    return 0
