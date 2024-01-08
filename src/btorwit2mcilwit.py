import pickle
from pathlib import Path

from .btor_witness import *
from .mcil_witness import *
from .mcil import *
from .btor import *
from .parse_btorwit import parse_witness
from .util import eprint

FILE_NAME = Path(__file__).name


def bitvec_to_mcil(bitvec: BitVec) -> MCILConstant:
    return MCIL_BITVEC_CONST(bitvec.width, bitvec.value)


def collect_enums(btor2_program: list[BtorNode]) -> dict[str, list[str]]:
    """Return mapping of enum variable names to an order-sensitive list of their potential values. Enums are encoded in the first comments of the model and are of the form: `; E var = Val0 Val1 ... ValN`."""
    if len(btor2_program) < 1:
        return {}

    enums: dict[str, list[str]] = {}
    i = 0

    while str(btor2_program[i])[0:3] == "; E":
        comment = btor2_program[i].comment[4:]
        var,vals = [v.strip() for v in comment.split("=")]
        enums[var] = vals.split(" ")
        i += 1

    return enums


def collect_arrays(btor2_program: list[BtorNode]) -> dict[str, tuple[int, int]]:
    """Return mapping of array variable names to their respective sort signatures. Note that BTOR2 solvers only support arrays from bit vectors to bit vectors. These sorts are encoded in the first comments of the model and are of the form: `; A var = X Y`."""
    if len(btor2_program) < 1:
        return {}

    arrays: dict[str, tuple[int, int]] = {}
    i = 0

    while str(btor2_program[i])[0:3] == "; A":
        comment = btor2_program[i].comment[4:]
        var,vals = [v.strip() for v in comment.split("=")]
        (index_width, element_width) = vals.split(" ")
        arrays[var] = (int(index_width), int(element_width))
        i += 1

    return arrays


def collect_var_symbols(btor2_program: list[BtorNode]) -> dict[int, str]:
    """Return a mapping of ints (in BTOR2 witness) to variable names. Variables are indexed in the order they appear in the BTOR2 input file. Searches for `.cur` vars that are not locals to any sub-systems; a variable with scope `::` is a local in a sub-system."""
    vars = {}
    cur = 0
    for node in [n for n in btor2_program if isinstance(n, BtorVar)]:
        if node.symbol.find("::") == -1 and node.symbol.find(".cur") != -1:
            vars[cur] = node.symbol.removesuffix(".cur")
        cur += 1
    return vars


def btor2_array_assigns_to_mcil_array(
    btor2_array_assigns: list[BtorArrayAssignment],
    index_sort: MCILSort,
    element_sort: MCILSort
) -> MCILExpr:
    """Return an `MCILExpr` equivalent to `btor2_array_assigns`, using a constant array as a base term and performing a series of stores on that array. The constant array is either the element of an array assignment with index `*`, or the first array assignment's element if no such assignment exists. Assume that there is at most one assignment with index `*`."""
    # default_assign holds an assignment of the form:
    #   id [*] element
    # Example:
    #   3 [*] 00100001
    default_assign = None
    for assign in btor2_array_assigns:
        if not assign.index:
            default_assign = assign
            break
    
    if not default_assign:
        default_assign = btor2_array_assigns[0]

    const_val = bitvec_to_mcil(default_assign.element)
    mcil_array = MCIL_ARRAY_CONST(index_sort, element_sort, const_val)

    for assign in btor2_array_assigns:
        if not assign.index:
            continue

        mcil_array = MCIL_STORE_EXPR(
            mcil_array,
            bitvec_to_mcil(assign.index),
            bitvec_to_mcil(assign.element)
        )
            
    return mcil_array


def translate(
    btor2_program: list[BtorNode],
    btor_witness: BtorWitness,
    query_symbol: str,
) -> Optional[MCILTrace]:
    trail: list[MCILState] = []

    vars = collect_var_symbols(btor2_program)
    enums = collect_enums(btor2_program)
    arrays = collect_arrays(btor2_program)

    # we index at [:-1] to skip the last frame due to encoding of :reach
    # properties.
    for frame in btor_witness.frames[:-1]:
        mcil_assigns: list[MCILAssignment] = []

        btor2_assigns = [
            assign
            for assign 
            in frame.state_assigns + frame.input_assigns 
            if assign.id in vars
        ]

        btor2_array_assigns: dict[int, list[BtorArrayAssignment]] = {}

        for btor2_assign in btor2_assigns:
            if (
                isinstance(btor2_assign, BtorBitVecAssignment) 
                and vars[btor2_assign.id] in enums
            ):
                enum_sort = vars[btor2_assign.id]
                enum_val = enums[enum_sort][btor2_assign.value.value]

                mcil_assign = MCILAssignment(
                    vars[btor2_assign.id], 
                    MCIL_ENUM_CONST(enum_sort, enum_val)
                )

                mcil_assigns.append(mcil_assign)
            elif isinstance(btor2_assign, BtorBitVecAssignment):
                mcil_assign = MCILAssignment(
                    vars[btor2_assign.id], 
                    bitvec_to_mcil(btor2_assign.value)
                )

                mcil_assigns.append(mcil_assign)
            elif isinstance(btor2_assign, BtorArrayAssignment):
                id = btor2_assign.id
                if id not in btor2_array_assigns:
                    btor2_array_assigns[id] = []

                btor2_array_assigns[id].append(btor2_assign)
            else:
                raise NotImplementedError

        for id,assigns in btor2_array_assigns.items():
            index_sort, element_sort = arrays[vars[id]]
            mcil_assign = MCILAssignment(
                vars[id],
                btor2_array_assigns_to_mcil_array(
                    assigns, 
                    MCIL_BITVEC_SORT(index_sort), 
                    MCIL_BITVEC_SORT(element_sort)
                )
            )
            
            mcil_assigns.append(mcil_assign)

        trail.append(
            MCILState(frame.index, mcil_assigns)
        )

    return MCILTrace(
        f"{query_symbol}_trace", MCILTrail(f"{query_symbol}_trail", trail), None
    )


def main(
    witness_path: Path, 
    program_path: Path,
    output_path: Path
) -> int:
    if witness_path.is_dir():
        witness_paths = [p for p in witness_path.glob("*")]
    elif witness_path.is_file():
        witness_paths = [witness_path]
    else:
        eprint(f"[{FILE_NAME}] BTOR2 witness path must be file or directory.\n")
        return 1

    query_responses: list[MCILQueryResponse] = []

    for witness in witness_paths:
        with open(witness, "r") as f:
            witness_content = f.read()

        # check for empty witness
        # this means the query was unsat
        if witness_content == "":
            query_responses.append(MCILQueryResponse(
                witness.suffixes[-2][1:],
                    MCILQueryResult.UNSAT,
                    None,
                    None,
                    None
            ))
            continue
        
        btor_witness = parse_witness(witness_content)
        if not btor_witness:
            eprint(f"[{FILE_NAME}] parse error for BTOR2 witness file '{witness}'.\n")
            return 1

        with open(program_path, "rb") as f:
            btor2_program = pickle.load(f)

        if btor_witness:
            query_symbol = witness.suffixes[-2][1:]

            mcil_trace = translate(btor2_program, btor_witness, query_symbol)

            query_responses.append(MCILQueryResponse(
                    query_symbol,
                    MCILQueryResult.SAT,
                    None,
                    mcil_trace,
                    None
                )
            )

    check_sys_response = MCILCheckSystemResponse(query_responses)

    with open(str(output_path), "w") as f:
        f.write(str(check_sys_response))

    return 0
