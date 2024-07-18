"""
Module for translating VMT-LIB to MoXI.

(Note: we ignore the ':predicate' annotation)
"""

import pathlib
from typing import Optional, cast

from src import log, parse_vmt, vmt, moxi

FILE_NAME = pathlib.Path(__file__).name


def defines_to_lets(
    term: moxi.Term, context: moxi.Context, vmt_program: vmt.Program
) -> moxi.Term:
    """Replaces all function occurrences in `term` with a let binding.

    Assuming vars a,b,c where e is the target term:
    (define-fun d () Bool (and a b))
    (define-fun e () Bool (or d c))
    ===>
    (define-fun e () Bool (let (d (and a b)) (or d c)))
    """
    dependent_defines: list[str] = []
    stack: list[tuple[bool, moxi.Term]] = []
    stack.append((False, term))
    visited: set[moxi.Term] = set()

    while len(stack) > 0:
        (seen, cur) = stack.pop()

        if cur in visited:
            continue
        elif seen:
            if (
                isinstance(cur, moxi.Variable)
                and cur.symbol in vmt_program.funs
                and cur.symbol not in dependent_defines
            ):
                dependent_defines.append(cur.symbol)
            visited.add(cur)
            continue

        if seen and isinstance(cur, moxi.LetTerm):
            for v, t in cur.get_binders():
                context.remove_bound_let_var(v)
            continue
        elif seen and isinstance(cur, moxi.Bind):
            for v, t in cur.get_binders():
                context.add_bound_let_var(v, t)
            continue

        stack.append((True, cur))

        for child in cur.children:
            stack.append((False, child))
        if isinstance(cur, moxi.Variable) and cur.symbol in vmt_program.funs:
            _, fun_term = vmt_program.funs[cur.symbol]
            stack.append((False, fun_term))

    new_term = term
    for (_, t), sym in reversed([(vmt_program.funs[s], s) for s in dependent_defines]):
        new_term = moxi.LetTerm(moxi.Sort.NoSort(), [(sym, t)], new_term)

    return new_term


def resolve_next_vars(
    term: moxi.Term, context: moxi.Context, prev: dict[str, tuple[str, moxi.Sort]]
) -> None:
    """Replaces all variables in `term` that are next vars according to `prev` with a primed variable."""
    for t in moxi.postorder(term, context):
        if not isinstance(t, moxi.Variable) or t.symbol not in prev:
            continue

        (prev_symbol, prev_sort) = prev[t.symbol]
        primed_var = moxi.Variable(prev_sort, prev_symbol, True)
        t.replace(primed_var)


def translate(
    vmt_program: vmt.Program, with_lets: bool = False
) -> Optional[moxi.Program]:
    input_vars = [
        (v, s)
        for v, s in vmt_program.vars
        if v not in vmt_program.next and v not in vmt_program.prev
    ]
    output_vars = [(v, s[1]) for v, s in vmt_program.next.items()]
    if with_lets:
        local_vars = [] # unused
    else:
        local_vars = [(v, s) for v, (s, _) in vmt_program.funs.items()]

    context = moxi.Context()

    # Init term
    moxi_init_term = moxi.conjoin_list(vmt_program.init_terms)
    if with_lets:
        moxi_init_term = defines_to_lets(moxi_init_term, context, vmt_program)
    moxi.remove_term_attrs(moxi_init_term, context)

    # Trans term
    moxi_trans_term = moxi.conjoin_list(vmt_program.trans_terms)
    if with_lets:
        moxi_trans_term = defines_to_lets(moxi_trans_term, context, vmt_program)
    resolve_next_vars(moxi_trans_term, context, vmt_program.prev)
    moxi.remove_term_attrs(moxi_trans_term, context)

    # Inv term
    if with_lets:
        moxi_inv_term = moxi.Constant.Bool(True)
    else:
        moxi_inv_term = moxi.conjoin_list(
            [
                moxi.Apply.Eq([moxi.Variable(srt, sym, False), trm])
                for sym, (srt, trm) in vmt_program.funs.items()
            ]
        )
        resolve_next_vars(moxi_inv_term, context, vmt_program.prev)
        moxi.remove_term_attrs(moxi_inv_term, context)

    system = moxi.DefineSystem(
        "main",
        input_vars,
        output_vars,
        local_vars,
        moxi_init_term,
        moxi_trans_term,
        moxi_inv_term,
        {},
    )

    # Build CheckSystem command
    reachable = {}
    for num, invar_prop in vmt_program.invar_properties.items():
        if with_lets:
            moxi_invar_prop = defines_to_lets(invar_prop, context, vmt_program)
        else:
            moxi_invar_prop = invar_prop
        resolve_next_vars(moxi_invar_prop, context, vmt_program.prev)
        moxi.remove_term_attrs(moxi_invar_prop, context)
        reachable[f"rch_{num}"] = cast(moxi.Term, moxi.Apply.Not(moxi_invar_prop))

    fairness = {
        f"fair_{num}": cast(moxi.Term, moxi.Apply.Not(live_prop))
        for num, live_prop in vmt_program.live_properties.items()
    }
    [moxi.remove_term_attrs(t, context) for t in fairness.values()]

    query = {f"qry_{lbl}": [lbl] for lbl, _ in reachable.items()} | {
        f"qry_{lbl}": [lbl] for lbl, _ in fairness.items()
    }

    check = moxi.CheckSystem(
        "main",
        input_vars,
        output_vars,
        local_vars,
        {},
        fairness,
        reachable,
        {},
        query,
        [],
    )

    return moxi.Program([moxi.SetLogic("ALL"), system, check])


def translate_file(input_path: pathlib.Path, output_path: pathlib.Path, with_lets: bool) -> int:
    if not input_path.is_file():
        log.error(f"'{input_path}' is not a valid file.", FILE_NAME)
        return 1

    if output_path.exists():
        log.error(f"Output path '{output_path}' already exists.", FILE_NAME)
        return 1

    program = parse_vmt.parse(input_path)

    if not program:
        log.error("Failed parsing", FILE_NAME)
        return 1

    moxi_program = translate(program, with_lets)

    if not moxi_program:
        log.error("Failed translation", FILE_NAME)
        return 1

    log.debug(1, f"Writing output to {output_path}", FILE_NAME)

    with open(str(output_path), "w") as f:
        f.write(str(moxi_program))
        log.debug(1, f"Wrote output to {output_path}", FILE_NAME)

    return 0
