import pickle
import pathlib
from typing import Optional

from src import bitvec, btor_witness, btor, moxi, moxi_witness, parse_btorwit, log

FILE_NAME = pathlib.Path(__file__).name


def bitvec_to_moxi(bitvec: bitvec.BitVec, is_bool: bool) -> moxi.Constant:
    if is_bool:
        return moxi.Constant.Bool(bool(bitvec.value))
    return moxi.Constant.BitVec(bitvec.width, bitvec.value)


def collect_enums(btor2_program: btor.BtorProgram) -> dict[str, list[str]]:
    """Return mapping of enum variable names to an order-sensitive list of their potential values. Enums are encoded in the first comments of the model and are of the form: `; E var = Val0 Val1 ... ValN`."""
    if len(btor2_program.nodes) < 1:
        return {}

    enums: dict[str, list[str]] = {}
    i = 0

    while str(btor2_program.nodes[i])[0] == ";":
        if str(btor2_program.nodes[i])[0:3] != "; E":
            i += 1
            continue
        comment = btor2_program.nodes[i].comment[4:]
        var, vals = [v.strip() for v in comment.split("=")]
        enums[var] = vals.split(" ")
        i += 1

    return enums


def collect_arrays(btor2_program: btor.BtorProgram) -> dict[str, tuple[int, int]]:
    """Return mapping of array variable names to their respective sort signatures. Note that BTOR2 solvers only support arrays from bit vectors to bit vectors. These sorts are encoded in the first comments of the model and are of the form: `; A var = X Y`."""
    if len(btor2_program.nodes) < 1:
        return {}

    arrays: dict[str, tuple[int, int]] = {}
    i = 0

    while str(btor2_program.nodes[i])[0] == ";":
        if str(btor2_program.nodes[i])[0:3] != "; A":
            i += 1
            continue
        comment = btor2_program.nodes[i].comment[4:]
        var, vals = [v.strip() for v in comment.split("=")]
        (index_width, element_width) = vals.split(" ")
        arrays[var] = (int(index_width), int(element_width))
        i += 1

    return arrays


def collect_input_vars(btor2_program: btor.BtorProgram) -> set[str]:
    """Return a set of variable names corresponding to the input variables. Reads the annotation of the `I var`"""
    if len(btor2_program.nodes) < 1:
        return set()

    input_vars = set()
    i = 0

    while str(btor2_program.nodes[i])[0] == ";":
        if str(btor2_program.nodes[i])[0:3] != "; I":
            i += 1
            continue
        comment = btor2_program.nodes[i].comment[4:]
        var = comment.strip()
        input_vars.add(var)
        i += 1

    return input_vars


def collect_bool_vars(btor2_program: btor.BtorProgram) -> set[str]:
    """Return a set of variable names corresponding to the variables with Bool sorts. Reads the annotation of the `B var`"""
    if len(btor2_program.nodes) < 1:
        return set()

    bool_vars = set()
    i = 0

    while str(btor2_program.nodes[i])[0] == ";":
        if str(btor2_program.nodes[i])[0:3] != "; B":
            i += 1
            continue
        comment = btor2_program.nodes[i].comment[4:]
        var = comment.strip()
        bool_vars.add(var)
        i += 1

    return bool_vars


def collect_var_symbols(btor2_program: btor.BtorProgram) -> dict[int, str]:
    """Return a mapping of ints (in BTOR2 witness) to variable names. Variables are indexed in the order they appear in the BTOR2 input file. Searches for `.cur` vars that are not locals to any sub-systems; a variable with scope `::` is a local in a sub-system."""
    vars = {}
    cur = 0
    for node in [n for n in btor2_program.nodes if isinstance(n, btor.BtorVar)]:
        if node.symbol.find("::") == -1 and node.symbol.find(".cur") != -1:
            vars[cur] = node.symbol.removesuffix(".cur")
        cur += 1
    return vars


def to_moxi_array(
    btor2_array_assigns: list[btor_witness.BtorArrayAssignment],
    index_sort: moxi.Sort,
    element_sort: moxi.Sort,
    bool_vars: set[int],
) -> moxi.Expr:
    """Return an `moxi.Expr` equivalent to `btor2_array_assigns`, using a constant array as a base term and performing a series of stores on that array. The constant array is either the element of an array assignment with index `*`, or the first array assignment's element if no such assignment exists. Assume that there is at most one assignment with index `*`."""
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

    const_val = bitvec_to_moxi(default_assign.element, default_assign.id in bool_vars)
    moxi_array = moxi.Constant.Array(index_sort, element_sort, const_val)

    for assign in btor2_array_assigns:
        if not assign.index:
            continue

        moxi_array = moxi.Apply.Store(
            moxi_array,
            bitvec_to_moxi(assign.index, default_assign.id in bool_vars),
            bitvec_to_moxi(assign.element, default_assign.id in bool_vars),
        )

    return moxi_array


def to_moxi_assigns(
    new_btor2_assigns: list[btor_witness.BtorAssignment],
    enums: dict[str, list[str]],
    vars: dict[int, str],
    arrays: dict[str, tuple[int, int]],
    bool_vars: set[int],
) -> list[moxi_witness.Assignment]:
    # TODO: Use `verbose` to enable verbose/compact witness options
    moxi_assigns: list[moxi_witness.Assignment] = []
    btor2_array_assigns: dict[int, list[btor_witness.BtorArrayAssignment]] = {}

    for btor2_assign in new_btor2_assigns:
        if (
            isinstance(btor2_assign, btor_witness.BtorBitVecAssignment)
            and vars[btor2_assign.id] in enums
        ):
            enum_sort = vars[btor2_assign.id]
            enum_val = enums[enum_sort][btor2_assign.value.value]

            moxi_assign = moxi_witness.Assignment(
                vars[btor2_assign.id], moxi.Constant.Enum(enum_sort, enum_val)
            )

            moxi_assigns.append(moxi_assign)
        elif isinstance(btor2_assign, btor_witness.BtorBitVecAssignment):
            moxi_assign = moxi_witness.Assignment(
                vars[btor2_assign.id],
                bitvec_to_moxi(btor2_assign.value, btor2_assign.id in bool_vars),
            )

            moxi_assigns.append(moxi_assign)
        elif isinstance(btor2_assign, btor_witness.BtorArrayAssignment):
            id = btor2_assign.id
            if id not in btor2_array_assigns:
                btor2_array_assigns[id] = []

            btor2_array_assigns[id].append(btor2_assign)
        else:
            raise NotImplementedError

    for id, assigns in btor2_array_assigns.items():
        index_sort, element_sort = arrays[vars[id]]
        moxi_assign = moxi_witness.Assignment(
            vars[id],
            to_moxi_array(
                assigns,
                moxi.Sort.BitVec(index_sort),
                moxi.Sort.BitVec(element_sort),
                bool_vars,
            ),
        )

        moxi_assigns.append(moxi_assign)

    # sort the assigns lexicographically according to their symbols
    moxi_assigns.sort(key=lambda x: x.symbol)

    return moxi_assigns


def translate(
    btor2_program: btor.BtorProgram,
    btor_witness: btor_witness.BtorWitness,
    query_symbol: str,
) -> Optional[moxi_witness.Trace]:
    trail: list[moxi_witness.State] = []

    vars = collect_var_symbols(btor2_program)
    enums = collect_enums(btor2_program)
    arrays = collect_arrays(btor2_program)

    input_var_symbols = collect_input_vars(btor2_program)
    input_vars = {i for i, s in vars.items() if s in input_var_symbols}

    bool_var_symbols = collect_bool_vars(btor2_program)
    bool_vars = {i for i, s in vars.items() if s in bool_var_symbols}

    # we index at [:-1] to skip the last frame due to encoding of :reach
    # properties.
    for frame in btor_witness.frames[:-1]:
        btor2_state_assigns = [
            assign
            for assign in frame.state_assigns
            if assign.id in vars and assign.id not in input_vars
        ]

        btor2_input_assigns = [
            assign
            for assign in frame.state_assigns
            if assign.id in vars and assign.id in input_vars
        ]

        moxi_state_assigns = to_moxi_assigns(
            btor2_state_assigns, enums, vars, arrays, bool_vars
        )
        moxi_input_assigns = to_moxi_assigns(
            btor2_input_assigns, enums, vars, arrays, bool_vars
        )

        trail.append(
            moxi_witness.State(frame.index, moxi_state_assigns, moxi_input_assigns)
        )

    return moxi_witness.Trace(
        f"{query_symbol}_trace",
        moxi_witness.Trail(f"{query_symbol}_trail", trail),
        None,
    )


def main(
    input_path: pathlib.Path,
    output_path: pathlib.Path,
    verbose: bool,
    do_pickle: bool,
    overwrite: bool,
) -> int:
    """Translates each BTOR2 file set in each `check-system` directory in `witness_path` into the corresponding `moxi.Witness` and writes the result to `output_path`. If `verbose` is enabled, writes the `moxi.Witness` in verbose format (TODO: Implement compact format).

    `witness_path` should have a directory structure of the form (one directory for each `check-system` command of the original moxi. file):
    `system.1/(BTOR2 file set)`
    ...
    `system.N/(BTOR2 file set)`

    BTOR2 file sets are of the form:
    {`query1.btor2`, `query1.btor2.cex`, `query1.btor2.pickle`},
    {`query2.btor2`, `query2.btor2.cex`, `query2.btor2.pickle`},
    {`query3.btor2`, `query3.btor2.pickle`},
    etc.

    If the file set for `query` includes a file with the `.cex` suffix, then `query` is sat. Otherwise, `query is unsat."""
    if not input_path.is_dir():
        log.error("Error: witness path must be a directory.", FILE_NAME)
        return 1

    check_system_responses: list[moxi_witness.CheckSystemResponse] = []

    for check_system_path in input_path.iterdir():
        program_paths = [prog for prog in check_system_path.glob("*.btor2")]
        pickle_paths = [p.with_suffix(".btor2.pickle") for p in program_paths]

        system_symbol = check_system_path.stem

        query_responses: list[moxi_witness.QueryResponse] = []

        for program_path, pickle_path in zip(program_paths, pickle_paths):
            witness_path = check_system_path / f"{program_path.name}.cex"

            with open(str(witness_path), "r") as f:
                witness_content = f.read()

            query_symbol = program_path.stem

            # check for empty witness
            # this means the query was unsat
            if witness_content == "":
                query_responses.append(
                    moxi_witness.QueryResponse(
                        query_symbol, moxi_witness.QueryResult.UNSAT, None, None, None
                    )
                )
                continue

            btor_witness = parse_btorwit.parse_witness(witness_content)
            if not btor_witness:
                log.error(f"Parse error for BTOR2 witness file {input_path}", FILE_NAME)
                return 1

            with open(pickle_path, "rb") as f:
                btor2_program = pickle.load(f)

            moxi_trace = translate(btor2_program, btor_witness, query_symbol)

            query_responses.append(
                moxi_witness.QueryResponse(
                    query_symbol, moxi_witness.QueryResult.SAT, None, moxi_trace, None
                )
            )

        check_system_responses.append(
            moxi_witness.CheckSystemResponse(system_symbol, query_responses)
        )

    moxi_wit = moxi_witness.Witness(check_system_responses)

    if not overwrite and output_path.exists():
        log.error(
            f"Already exists: {output_path}\n\t"
            "Did you mean to enable the '--overwrite' option?",
            FILE_NAME,
        )
        return 1

    with open(str(output_path), "w") as f:
        f.write(str(moxi_wit))

    if do_pickle:
        with open(f"{output_path}.pickle", "wb") as f:
            pickle.dump(moxi_wit, f)

    return 0
