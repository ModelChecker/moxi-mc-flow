import pathlib
from typing import Optional, cast

from src import log, moxi, panda, parse_smv, smv

FILE_NAME = pathlib.Path(__file__).name


def to_moxi_ident(smv_ident: str) -> str:
    new_ident = (
        smv_ident.replace("__dot__", ".")
        .replace("__colon__", ":")
        .replace("__dquote__", '"')
        .replace("__dollar__", "$")
        .replace("__lbrack__", "[")
        .replace("__rbrack__", "]")
    )
    if new_ident[0] == '"':
        return "|" + new_ident[1:-1] + "|"
    if any([c in new_ident for c in {":", "[" "]", "#"}]):
        return "|" + new_ident + "|"
    return new_ident


def translate_type(smv_type: smv.Type, smv_context: smv.Context) -> moxi.Sort:
    """
    Translates an SMV type to an IL sort given a current SMV context.

    SMV booleans/ints translate straightforwardly
    SMV real/clock unsupported
    SMV words (of width w) translate to MoXI bitvecs of width w
    SMV arrays with element type t translate to MoXI arrays with translated element types
    SMV module types cannot occur in general expressions
    SMV enums are handled specially (see comment) -- this is the only branch requiring the context.
    """
    match smv_type:
        case smv.Boolean():
            return moxi.Sort.Bool()
        case smv.Integer():
            smv_context.has_integers = True
            return moxi.Sort.Int()
        case smv.Real():
            raise ValueError("nuXmv `real` type not immediately supported in MoXI")
        case smv.Clock():
            raise ValueError("nuXmv `clock` type not immediately supported in MoXI")
        case smv.Word(width=w):
            smv_context.has_bitvecs = True
            return moxi.Sort.BitVec(int(w))
        case smv.Array(subtype=t):
            smv_context.has_arrays = True
            return moxi.Sort.Array(moxi.Sort.Int(), translate_type(t, smv_context))
        case smv.WordArray(word_length=wl, subtype=t):
            smv_context.has_arrays = True
            return moxi.Sort.Array(
                moxi.Sort.BitVec(int(wl)), translate_type(t, smv_context)
            )
        case smv.ModuleType():
            raise ValueError(f"Cannot translate type {smv_type}")
        case smv.Enumeration():
            if smv_type.is_integer():
                return moxi.Sort.Int()

            """
            As for enums, we'll have to handle those a bit differently than we are right now (at least symbolic ones). Because right now, in SMV, you may have two variables like:

            v1: {s0, s1};
            v2: {s0, s1, s2};

            And something like: (v1 = v2) is a totally valid expression. But in the translation, they are both translated to different enum types entirely, which won't be well-sorted. Instead, we need all symbolic enum type to be translated to the same moxi. enum sort, then constrain them like:

            (declare-enum-sort enums (s0 s1 s2))
            (define-system ...
            :local ((v1 enums) (v2 enums))
            :inv (and (or (= v1 s0) (= v1 s1)) (or (= v2 s0) (= v2 s1) (=v2 s2))

            I'm not sure any of the benchmarks exhibit this, but it's something to keep in mind.
            """

            sums = smv_type.summands
            lsums = list(sums)
            slsums = [str(s) for s in lsums]

            return moxi.Sort.Enum(smv_context.reverse_enums[str(slsums[0])][0])
        case _:
            raise ValueError(f"Unsupported type: {smv_type}")


def case_to_ite(
    case_expr: smv.CaseExpr, context: smv.Context, expr_map: dict[smv.Expr, moxi.Term]
) -> moxi.Term:
    """Recursively translate a case expression to a series of cascaded ite expressions."""

    def _case_to_ite(branches: list[tuple[smv.Expr, smv.Expr]], i: int) -> moxi.Term:
        (cond, branch) = branches[i]

        if i >= len(branches) - 1:
            return moxi.Apply(
                translate_type(branch.type, context),
                moxi.Identifier("ite", []),
                [expr_map[cond], expr_map[branch], expr_map[branch]],
            )

        return moxi.Apply(
            translate_type(branch.type, context),
            moxi.Identifier("ite", []),
            [expr_map[cond], expr_map[branch], _case_to_ite(branches, i + 1)],
        )

    return _case_to_ite(case_expr.branches, 0)


def get_define_let_var(symbol: str) -> moxi.Variable:
    return moxi.Variable(moxi.Sort.NoSort(), symbol, False)


def build_define_expr(
    expr: smv.Identifier, context: smv.Context, module: smv.ModuleDeclaration
) -> moxi.Term:
    log.debug(2, f"building define expr {expr}", FILE_NAME)

    def dependent_defines(ident: str, context: smv.Context) -> list[smv.Identifier]:
        stack: list[tuple[bool, smv.Expr]] = []
        visited: set[smv.Expr] = set()
        deps: list[smv.Identifier] = []

        stack.append((False, context.defs[module.name][ident]))

        while len(stack) > 0:
            (seen, cur) = stack.pop()

            if cur in visited:
                continue
            elif seen:
                if (
                    isinstance(cur, smv.Identifier)
                    and cur.ident in context.defs[module.name]
                ):
                    deps.append(cur)
                visited.add(cur)
                continue

            stack.append((True, cur))

            match cur:
                case smv.Identifier(ident=ident):
                    if ident in context.defs[module.name]:
                        stack.append((False, context.defs[module.name][ident]))
                case smv.FunCall(args=args):
                    [stack.append((False, arg)) for arg in args]
                case smv.UnOp(arg=arg):
                    stack.append((False, arg))
                case smv.BinOp(lhs=lhs, rhs=rhs):
                    stack.append((False, lhs))
                    stack.append((False, rhs))
                case smv.IndexSubscript(array=array, index=index):
                    stack.append((False, array))
                    stack.append((False, index))
                case smv.WordBitSelection(word=word, low=_, high=_):
                    stack.append((False, word))
                case smv.SetBodyExpression(members=members):
                    [stack.append((False, m)) for m in members]
                case smv.Ternary(cond=cond, then_expr=then_expr, else_expr=else_expr):
                    stack.append((False, cond))
                    stack.append((False, then_expr))
                    stack.append((False, else_expr))
                case smv.CaseExpr(branches=branches):
                    for cond, then_expr in branches:
                        stack.append((False, cond))
                        stack.append((False, then_expr))
                case _:
                    pass

        return deps

    emap = {}
    translate_expr(
        context.defs[module.name][expr.ident],
        context,
        emap,
        in_let_expr=True,
        module=module,
    )
    ret = moxi.LetTerm(
        moxi.Sort.NoSort(),
        [(expr.ident, emap[context.defs[module.name][expr.ident]])],
        get_define_let_var(expr.ident),
    )

    for d in reversed(dependent_defines(expr.ident, context)):
        log.debug(2, str(d), FILE_NAME)
        translate_expr(
            context.defs[module.name][d.ident],
            context,
            emap,
            in_let_expr=True,
            module=module,
        )
        ret = moxi.LetTerm(
            moxi.Sort.NoSort(),
            [(d.ident, emap[context.defs[module.name][d.ident]])],
            ret,
        )

    return ret


def translate_expr(
    smv_expr: smv.Expr,
    context: smv.Context,
    expr_map: dict[smv.Expr, moxi.Term],
    in_let_expr: bool,
    module: smv.ModuleDeclaration,
) -> None:
    """Updates `expr_map` to map all sub-expressions of `smv_expr` to translated moxi. expressions."""
    for expr in smv.postorder(smv_expr, context, False):
        if expr in expr_map:
            continue

        match expr:
            case smv.Identifier(ident=ident):
                # print(f"IDENTIFIER {ident}")

                if ident in context.defs[module.name] and not in_let_expr:
                    # print(f"{ident}: def case not let")
                    expr_map[expr] = build_define_expr(expr, context, module=module)
                elif ident in context.defs[module.name]:
                    # print(f"{ident}: def case")
                    expr_map[expr] = get_define_let_var(expr.ident)
                elif ident in context.vars[module.name] and isinstance(
                    context.vars[module.name][ident], smv.ModuleType
                ):
                    # Skip over any module variables that come up in traversal
                    # These are all module accesses -- relevant for type checking but not here
                    pass
                elif module.name in context.vars and ident in context.vars[module.name]:
                    # print(f"{ident}: var case")
                    expr_map[expr] = moxi.Variable(
                        sort=translate_type(context.vars[module.name][ident], context),
                        symbol=to_moxi_ident(ident),
                        prime=context.in_next_expr,
                    )
                elif ident in context.reverse_enums:
                    # print(f"{ident}: enum case")
                    expr_map[expr] = moxi.Constant(
                        sort=moxi.Sort.Enum(context.reverse_enums[ident][0]),
                        value=ident,
                    )
                elif (
                    module.name in context.module_params
                    and expr.ident in context.module_params[module.name]
                ):
                    # print(f"{ident}: param case")
                    ttype = translate_type(
                        context.module_params[module.name][expr.ident], context
                    )
                    # print(f"assigning {expr} : {ttype}")
                    expr_map[expr] = moxi.Variable(
                        sort=ttype,
                        symbol=to_moxi_ident(ident),
                        prime=context.in_next_expr,
                    )
                else:
                    raise ValueError(f"Unrecognized var `{ident}`")
            case smv.IntegerConstant(integer=i):
                if i < 0:
                    expr_map[expr] = moxi.Apply.IntNeg(
                        moxi.Constant(sort=moxi.Sort.Int(), value=-i)
                    )
                else:
                    expr_map[expr] = moxi.Constant(sort=moxi.Sort.Int(), value=i)
            case smv.BooleanConstant(boolean=b):
                expr_map[expr] = moxi.Constant(sort=moxi.Sort.Bool(), value=b)
            case smv.WordConstant(width=width, value=value):
                expr_map[expr] = moxi.Constant(
                    sort=moxi.Sort.BitVec(width), value=value
                )
            case smv.FunCall(name="signed", args=fargs):
                expr_map[expr] = expr_map[fargs[0]]
            case smv.FunCall(name="unsigned", args=fargs):
                expr_map[expr] = expr_map[fargs[0]]
            case smv.FunCall(name="next", args=fargs):
                expr_map[expr] = expr_map[fargs[0]]
            case smv.FunCall(name="READ", args=fargs):
                expr_map[expr] = moxi.Apply.Select(
                    expr_map[fargs[0]], expr_map[fargs[1]]
                )
            case smv.FunCall(name="WRITE", args=fargs):
                expr_map[expr] = moxi.Apply.Store(
                    expr_map[fargs[0]], expr_map[fargs[1]], expr_map[fargs[2]]
                )
            case smv.FunCall(name="typeof", args=fargs):
                expr_map[expr] = expr_map[fargs[0]]
            case smv.FunCall(name="CONSTARRAY", args=fargs):
                arr, val = fargs[0], fargs[1]
                if isinstance(arr.type, smv.Array):
                    raise NotImplementedError()
                elif isinstance(arr.type, smv.WordArray):
                    expr_map[expr] = moxi.Constant.Array(
                        moxi.Sort.BitVec(arr.type.word_length),
                        translate_type(arr.type.subtype, context),
                        expr_map[val],
                    )
                else:
                    raise NotImplementedError()
            case smv.FunCall(name="word1", args=fargs):
                expr_map[expr] = moxi.Apply(
                    moxi.Sort.BitVec(1),
                    moxi.Identifier("ite", []),
                    [
                        moxi.Apply(
                            moxi.Sort.Bool(),
                            moxi.Identifier("=", []),
                            [expr_map[fargs[0]], moxi.Constant.Bool(True)],
                        ),
                        moxi.Constant.BitVec(1, 1),
                        moxi.Constant.BitVec(1, 0),
                    ],
                )
            case smv.FunCall(name="toint", args=fargs):
                if isinstance(fargs[0].type, smv.Integer):
                    expr_map[expr] = expr_map[fargs[0]]
                elif isinstance(fargs[0].type, smv.Boolean):
                    expr_map[expr] = moxi.Apply(
                        moxi.Sort.Int(),
                        moxi.Identifier("ite", []),
                        [
                            expr_map[fargs[0]],
                            moxi.Constant.Int(1),
                            moxi.Constant.Int(0),
                        ],
                    )
                if isinstance(fargs[0].type, smv.Word):
                    log.error(
                        "int cast from words not supported in any logic", FILE_NAME
                    )
                    expr_map[expr] = moxi.Constant.Int(0)
            case smv.FunCall(name="swconst", args=fargs):
                pass
            case smv.FunCall(name="uwconst", args=fargs):
                pass
            case smv.FunCall(name="unsigned word", args=fargs):
                log.error("word cast not supported in any logic", FILE_NAME)
                width = cast(smv.IntegerConstant, fargs[0]).integer
                expr_map[expr] = moxi.Constant.BitVec(width, 0)
            case smv.FunCall(name="signed word", args=fargs):
                log.error("word cast not supported in any logic", FILE_NAME)
                width = cast(smv.IntegerConstant, fargs[0]).integer
                expr_map[expr] = moxi.Constant.BitVec(width, 0)
            case smv.FunCall(name=fname, args=fargs):
                expr_map[expr] = moxi.Apply(
                    sort=moxi.Sort.NoSort(),
                    identifier=moxi.Identifier(symbol=fname, indices=[]),
                    children=[expr_map[arg] for arg in fargs],
                )
            case smv.BinOp(op=op, lhs=lhs, rhs=rhs):
                match op:
                    case "&":
                        il_op = "and" if isinstance(lhs.type, smv.Boolean) else "bvand"
                        il_lhs = expr_map[lhs]
                        il_rhs = expr_map[rhs]
                        # il_op = fn_map[("and", get_optype(lhs.type))]
                    case "|":
                        il_op = "or" if isinstance(lhs.type, smv.Boolean) else "bvor"
                        il_lhs = expr_map[lhs]
                        il_rhs = expr_map[rhs]
                        # il_op = fn_map[("or", get_optype(lhs.type))]
                    case "xor":
                        il_op = "xor" if isinstance(lhs.type, smv.Boolean) else "bvxor"
                        il_lhs = expr_map[lhs]
                        il_rhs = expr_map[rhs]
                        # il_op = fn_map[("xor", get_optype(lhs.type))]
                    case "->":
                        il_op = "=>"
                        il_lhs = expr_map[lhs]
                        il_rhs = expr_map[rhs]
                    case "!=":
                        il_op = "distinct"
                        il_lhs = expr_map[lhs]
                        il_rhs = expr_map[rhs]
                    case "<":
                        if smv.is_integer_type(lhs.type):
                            il_op = ">"
                        elif isinstance(lhs.type, smv.Word) and lhs.type.signed:
                            il_op = "bvslt"
                        else:
                            il_op = "bvult"
                        il_lhs = expr_map[lhs]
                        il_rhs = expr_map[rhs]
                        # il_op = "bvult"
                        # il_op = fn_map[("<", get_optype(lhs.type))]
                    case ">":
                        if smv.is_integer_type(lhs.type):
                            il_op = ">"
                        elif isinstance(lhs.type, smv.Word) and lhs.type.signed:
                            il_op = "bvsgt"
                        else:
                            il_op = "bvugt"
                        il_lhs = expr_map[lhs]
                        il_rhs = expr_map[rhs]
                        # il_op = "bvugt"
                        # il_op = fn_map[(">", get_optype(lhs.type))]
                    case "<=":
                        if smv.is_integer_type(lhs.type):
                            il_op = "<="
                        elif isinstance(lhs.type, smv.Word) and lhs.type.signed:
                            il_op = "bvsle"
                        else:
                            il_op = "bvule"
                        il_lhs = expr_map[lhs]
                        il_rhs = expr_map[rhs]
                        # il_op = "bvule"
                        # il_op = fn_map[("<=", get_optype(lhs.type))]
                    case ">=":
                        if smv.is_integer_type(lhs.type):
                            il_op = ">="
                        elif isinstance(lhs.type, smv.Word) and lhs.type.signed:
                            il_op = "bvsge"
                        else:
                            il_op = "bvuge"
                        il_lhs = expr_map[lhs]
                        il_rhs = expr_map[rhs]
                        # il_op = "bvuge"
                        # il_op = fn_map[(">=", get_optype(lhs.type))]
                    case "+":
                        il_op = "+" if isinstance(lhs.type, smv.Integer) else "bvadd"
                        il_lhs = expr_map[lhs]
                        il_rhs = expr_map[rhs]
                        # il_op = "bvadd"
                        # il_op = fn_map[("+", get_optype(lhs.type))]
                    case "*":
                        il_op = "*" if isinstance(lhs.type, smv.Integer) else "bvmul"
                        il_lhs = expr_map[lhs]
                        il_rhs = expr_map[rhs]
                        # il_op = "bvmul"
                        # il_op = fn_map[("*", get_optype(lhs.type))]
                    case "/":
                        expr_type = cast(smv.Word, expr.type)
                        il_op = "bvsdiv" if expr_type.signed else "bvudiv"
                        il_lhs = expr_map[lhs]
                        il_rhs = expr_map[rhs]
                    case ">>":
                        if isinstance(lhs.type, smv.Word) and lhs.type.signed:
                            il_op = "bvashr"
                        else:
                            il_op = "bvlshr"
                        il_lhs = expr_map[lhs]
                        il_rhs = expr_map[rhs]
                    case "<<":
                        il_op = "bvshl"
                        il_lhs = expr_map[lhs]
                        il_rhs = expr_map[rhs]
                    case "mod":
                        if isinstance(lhs.type, smv.Word) and lhs.type.signed:
                            il_op = "bvsrem"
                        else:
                            il_op = "bvurem"
                        il_lhs = expr_map[lhs]
                        il_rhs = expr_map[rhs]
                    case "=" | "<->":
                        il_op = "="
                        try:
                            il_lhs_sort = translate_type(lhs.type, context)
                            if moxi.is_int_sort(il_lhs_sort):
                                il_lhs = expr_map[lhs]
                                il_rhs = expr_map[rhs]
                            else:
                                il_lhs = expr_map[lhs]
                                il_rhs = expr_map[rhs]
                        except ValueError:
                            try:
                                il_rhs_sort = translate_type(rhs.type, context)
                                if moxi.is_int_sort(il_rhs_sort):
                                    il_rhs = expr_map[rhs]
                                    il_lhs = expr_map[lhs]
                                else:
                                    il_lhs = expr_map[lhs]
                                    il_rhs = expr_map[rhs]
                            except ValueError:
                                il_lhs = expr_map[lhs]
                                il_rhs = expr_map[rhs]
                    case _:
                        il_op = op
                        il_lhs = expr_map[lhs]
                        il_rhs = expr_map[rhs]

                expr_map[expr] = moxi.Apply(
                    sort=translate_type(expr.type, context),
                    identifier=moxi.Identifier(symbol=il_op, indices=[]),
                    children=[il_lhs, il_rhs],
                )
            case smv.UnOp(op=op, arg=arg):
                match op:
                    case "!":
                        il_op = "not" if isinstance(arg.type, smv.Boolean) else "bvnot"
                    case "-":
                        il_op = "-" if isinstance(arg.type, smv.Integer) else "bvneg"
                    case _:
                        il_op = op

                expr_map[expr] = moxi.Apply(
                    sort=translate_type(expr.type, context),
                    identifier=moxi.Identifier(symbol=il_op, indices=[]),
                    children=[expr_map[arg]],
                )
            case smv.WordBitSelection(word=word, low=low, high=high):
                expr_map[expr] = moxi.Apply(
                    sort=translate_type(expr.type, context),
                    identifier=moxi.Identifier(symbol="extract", indices=[high, low]),
                    children=[expr_map[word]],
                )
            case smv.CaseExpr():
                expr_map[expr] = case_to_ite(expr, context, expr_map)
            case smv.ModuleAccess(module=ma_module, element=ma_elem):
                expr_map[expr] = moxi.Variable(
                    sort=translate_type(expr.type, context),
                    symbol=ma_module.ident + "." + ma_elem.ident,
                    prime=False,
                )
            case smv.Ternary(cond=cond, then_expr=then_expr, else_expr=else_expr):
                expr_map[expr] = moxi.Apply(
                    translate_type(then_expr.type, context),
                    moxi.Identifier("ite", []),
                    [expr_map[cond], expr_map[then_expr], expr_map[else_expr]],
                )
            case _:
                raise ValueError(f"unhandled expression {expr}, {expr.__class__}")


def gather_input(
    smv_module: smv.ModuleDeclaration, context: smv.Context
) -> list[tuple[str, moxi.Sort]]:
    """
    Input variables are either:
    1) Module parameters
    2) IVAR declarations
    """
    result: list[tuple[str, moxi.Sort]] = []

    for param in smv_module.parameters:
        result.append(
            (
                to_moxi_ident(param),
                translate_type(context.module_params[smv_module.name][param], context),
            )
        )

    for var_name, smv_var_type in [
        (var_name, smv_var_type)
        for e in smv_module.elements
        if isinstance(e, smv.VarDeclaration)
        for (var_name, smv_var_type) in e.var_list
        if e.modifier == "IVAR" and not isinstance(smv_var_type, smv.ModuleType)
    ]:
        result.append(
            (
                to_moxi_ident(var_name.ident),
                translate_type(smv_var_type, context),
            )
        )

    return result


def gather_local(
    smv_module: smv.ModuleDeclaration, context: smv.Context
) -> list[tuple[str, moxi.Sort]]:
    """
    Local modules are exactly the temporaries created for submodule rewiring.
    We don't directly pass in our input values into the submodule's inputs (or the submodule's outputs as our outputs)
    -- we instead construct local variables corresponding to all of these, instantiate them accordingly, and pass them into the submodules.
    """
    result: list[tuple[str, moxi.Sort]] = []
    for var_name, smv_var_type in [
        (var_name, smv_var_type)
        for e in smv_module.elements
        if isinstance(e, smv.VarDeclaration)
        for var_name, smv_var_type in e.var_list
        if isinstance(smv_var_type, smv.ModuleType)
    ]:
        context.module_locals[var_name.ident] = []
        # gathering submodule inputs
        for name in context.module_params[smv_var_type.module_name]:
            type = context.module_params[smv_var_type.module_name][name]
            input_var = moxi.Variable(
                sort=translate_type(type, context),
                symbol=to_moxi_ident(var_name.ident + "." + name),
                prime=False,
            )
            result.append(
                (
                    to_moxi_ident(var_name.ident + "." + name),
                    translate_type(type, context),
                )
            )
            context.module_locals[var_name.ident].append(input_var)

        # gathering submodule outputs

        for var_symbol, var_sort in context.outputs[smv_var_type.module_name]:
            local_var = moxi.Variable(
                sort=var_sort,
                symbol=to_moxi_ident(var_name.ident + "." + var_symbol),
                prime=False,
            )
            result.append((to_moxi_ident(var_name.ident + "." + var_symbol), var_sort))
            context.module_locals[var_name.ident].append(local_var)

    # for ltlspec in [
    #     e for e in smv_module.elements if isinstance(e, smv.LTLSpecDeclaration)
    # ]:
    #     pass

    return result


def gather_output(
    smv_module: smv.ModuleDeclaration, context: smv.Context
) -> list[tuple[str, moxi.Sort]]:
    """
    VAR/FROZENVAR constructs correspond to output variables in MoXI.
    Locally DEFINEd constructs are turned into output variables too.
    Moreover, outputs of submodules are lifted to constitute outputs of the supermodule.
    """
    result: list[tuple[str, moxi.Sort]] = []

    for var_name, smv_var_type in [
        (var_name, smv_var_type)
        for e in smv_module.elements
        if isinstance(e, smv.VarDeclaration)
        for (var_name, smv_var_type) in e.var_list
        if e.modifier == "FROZENVAR" or e.modifier == "VAR"
    ]:
        match smv_var_type:
            case smv.Enumeration(summands=summands):
                if smv_var_type.is_integer():
                    # values = {int(s) for s in expr.type.summands}
                    # expr.type = nuxmv.Integer(values)
                    il_type = moxi.Sort.Int()
                else:
                    lsummands = list(summands)
                    slsummands = [str(s) for s in lsummands]

                    il_symbol = context.reverse_enums[slsummands[0]][0]
                    il_type = moxi.Sort.Enum(il_symbol)
            case smv.ModuleType(module_name=module_name):
                gather_output(context.modules[module_name], context)
                continue
            case _:
                il_type = translate_type(smv_var_type, context)

        result.append((to_moxi_ident(var_name.ident), il_type))

    for define in [
        define
        for e in smv_module.elements
        if isinstance(e, smv.DefineDeclaration)
        for define in e.define_list
        if define.name.ident in context.referenced_defs[smv_module.name]
    ]:
        moxi_type = translate_type(
            context.defs[smv_module.name][define.name.ident].type, context
        )
        result.append((to_moxi_ident(define.name.ident), moxi_type))

    context.outputs[smv_module.name] = result

    return result


def specialize_variable(module_name: str, var: moxi.Variable) -> moxi.Variable:
    return moxi.Variable(
        sort=var.sort, symbol=module_name + "." + var.symbol, prime=var.prime
    )


def specialize_vars_in_expr(module_name: str, expr: moxi.Term) -> moxi.Term:
    match expr:
        case moxi.Variable():
            return specialize_variable(module_name, expr)
        case moxi.Apply(sort=sort, identifier=identifier, children=children):
            schildren: list[moxi.Term] = []
            for child in children:
                schildren.append(specialize_vars_in_expr(module_name, child))
            return moxi.Apply(sort=sort, identifier=identifier, children=schildren)
        case _:
            return moxi.Constant.Bool(True)
            # print("CATCH ALL CASE:", expr, expr.__class__.__name__)


def gather_init(
    smv_module: smv.ModuleDeclaration,
    context: smv.Context,
    expr_map: dict[smv.Expr, moxi.Term],
) -> moxi.Term:
    """
    Initial constraints handle the following 2 (1, depending on how you look at it) situations:
    1) INIT declarations - straightforward (nuXmv initial constraints ~> MoXI init constraints)
    2) ASSIGN `init` declarations - same as (1), since nuXmv semantics (2.3.9) indicate `ASSIGN init(a) := b` is the same as `INIT next(a) = b`
    """
    init_list: list[moxi.Term] = []

    for init_decl in [
        e for e in smv_module.elements if isinstance(e, smv.InitDeclaration)
    ]:
        translate_expr(
            init_decl.formula, context, expr_map, in_let_expr=False, module=smv_module
        )
        init_list.append(expr_map[init_decl.formula])

    for assign_decl in [
        a
        for e in smv_module.elements
        if isinstance(e, smv.AssignDeclaration)
        for a in e.assign_list
        if a.modifier == "init"
    ]:
        translate_expr(
            assign_decl.lhs,
            context,
            expr_map,
            in_let_expr=False,
            module=smv_module,
        )
        translate_expr(
            assign_decl.rhs,
            context,
            expr_map,
            in_let_expr=False,
            module=smv_module,
        )

        init_expr = moxi.Apply.Eq(
            [expr_map[assign_decl.lhs], expr_map[assign_decl.rhs]]
        )

        init_list.append(init_expr)

    return moxi.conjoin_list(init_list)


def gather_trans(
    smv_module: smv.ModuleDeclaration,
    context: smv.Context,
    expr_map: dict[smv.Expr, moxi.Term],
) -> moxi.Term:
    """
    Transition constraints handle the following 3 (or 2, depending on how you look at it) situations:
    1) TRANS declarations - straightforward (nuXmv transitions ~> MoXI transitions)
    2) ASSIGN `next` declarations - same as (1), since nuXmv semantics (2.3.9) indicate `ASSIGN next(a) := b` is the same as `TRANS next(a) = b`
    3) FROZENVAR declarations - we enforce the FROZENVAR constraint (that declared variables maintain the same value in subsequent states) by enforcing that `var' = var` in the transition relation.
    """
    trans_list: list[moxi.Term] = []

    for trans_decl in [
        e for e in smv_module.elements if isinstance(e, smv.TransDeclaration)
    ]:
        log.debug(2, "translating transition relation", FILE_NAME)
        translate_expr(
            trans_decl.formula, context, expr_map, in_let_expr=False, module=smv_module
        )
        trans_list.append(expr_map[trans_decl.formula])

    for assign_decl in [
        a
        for e in smv_module.elements
        if isinstance(e, smv.AssignDeclaration)
        for a in e.assign_list
        if a.modifier == "next"
    ]:
        translate_expr(
            assign_decl.rhs,
            context,
            expr_map,
            in_let_expr=False,
            module=smv_module,
        )

        if isinstance(assign_decl.lhs, smv.Identifier):
            lhs_expr = moxi.Variable(
                sort=translate_type(assign_decl.rhs.type, context),
                symbol=assign_decl.lhs.ident,
                prime=True,
            )
        else:
            raise ValueError("Unsupported: next(complex_identifier)")

        trans_expr = moxi.Apply.Eq([lhs_expr, expr_map[assign_decl.rhs]])

        trans_list.append(trans_expr)

    for var_ident in [
        var_name.ident
        for e in smv_module.elements
        if isinstance(e, smv.VarDeclaration)
        for (var_name, _) in e.var_list
        if e.modifier == "FROZENVAR"
    ]:
        trans_list.append(
            moxi.Apply.Eq(
                [
                    moxi.Variable(
                        sort=translate_type(
                            context.vars[smv_module.name][var_ident],
                            context,
                        ),
                        symbol=var_ident,
                        prime=False,
                    ),
                    moxi.Variable(
                        sort=translate_type(
                            context.vars[smv_module.name][var_ident],
                            context,
                        ),
                        symbol=var_ident,
                        prime=True,
                    ),
                ]
            )
        )

    return (
        moxi.conjoin_list(trans_list)
        if len(trans_list) > 0
        else moxi.Constant.Bool(True)
    )


def gather_inv(
    smv_module: smv.ModuleDeclaration,
    context: smv.Context,
    expr_map: dict[smv.Expr, moxi.Term],
) -> moxi.Term:
    """
    MoXI invariants (:inv) are used for the following functionalities:
    1) INVAR declarations - this is what you'd expect (nuXmv invariants -> MoXI invariants)
    2) ASSIGN declarations - same as (1) since nuXmv semantics (2.3.9) indicate `ASSIGN a := b` is the same as `INVAR a = b`
    3) Enumerations - since integer enums are otherwise generalized to be any integer, we recover the constraints of the enum by asserting them here.
    4) Local definitions via DEFINEs
    4) Submodule parameter rewiring
    """
    inv_list: list[moxi.Term] = []

    # things marked explicitly as INVAR
    # print("inv - looking for INVAR")
    for inv_decl in [
        e for e in smv_module.elements if isinstance(e, smv.InvarDeclaration)
    ]:
        translate_expr(
            inv_decl.formula, context, expr_map, in_let_expr=False, module=smv_module
        )
        inv_list.append(expr_map[inv_decl.formula])

    # standard ASSIGN declarations (without init/next modifiers)
    # print("inv - looking through ASSIGN")
    for assign_decl in [
        a
        for e in smv_module.elements
        if isinstance(e, smv.AssignDeclaration)
        for a in e.assign_list
        if a.modifier == "none"
    ]:
        translate_expr(
            assign_decl.rhs,
            context,
            expr_map,
            in_let_expr=False,
            module=smv_module,
        )

        if isinstance(assign_decl.lhs, smv.Identifier):
            lhs_expr = moxi.Variable(
                sort=translate_type(assign_decl.rhs.type, context),
                symbol=assign_decl.lhs.ident,
                prime=False,
            )
        else:
            raise ValueError("Unsupported: next(complex_identifier)")

        inv_expr = moxi.Apply.Eq([lhs_expr, expr_map[assign_decl.rhs]])

        inv_list.append(inv_expr)

    for var_list in [
        e.var_list for e in smv_module.elements if isinstance(e, smv.VarDeclaration)
    ]:
        # All integer enums must be constrained where they are declared
        # Example:
        #   var: {0,1,2}
        # should have moxi. constraint
        #   :inv (and ... (or (= var 0) (= var 1) (= var 2)) ...)
        for var_name, var_type in [
            (var_name, var_type)
            for (var_name, var_type) in var_list
            if isinstance(var_type, smv.Enumeration) and var_type.is_integer()
        ]:
            var_ident = var_name.ident
            inv_list.append(
                moxi.Apply.Or(
                    [
                        moxi.Apply.Eq(
                            [
                                moxi.Variable(
                                    moxi.Sort.Int(), to_moxi_ident(var_ident), False
                                ),
                                moxi.Constant.Int(int(value)),
                            ]
                        )
                        for value in var_type.summands
                    ]
                )
            )

    for define in [
        define
        for e in smv_module.elements
        if isinstance(e, smv.DefineDeclaration)
        for define in e.define_list
        if define.name.ident in context.referenced_defs[smv_module.name]
    ]:
        translate_expr(
            context.defs[smv_module.name][define.name.ident],
            context,
            expr_map,
            False,
            smv_module,
        )
        il_type = translate_type(
            context.defs[smv_module.name][define.name.ident].type, context
        )
        inv_list.append(
            moxi.Apply.Eq(
                [
                    moxi.Variable(
                        sort=il_type,
                        symbol=to_moxi_ident(define.name.ident),
                        prime=False,
                    ),
                    expr_map[context.defs[smv_module.name][define.name.ident]],
                ]
            )
        )

    # module variable instantiations
    # print("inv - looking through module instantiations")
    for var_name, var_type in [
        (var_name, var_type)
        for vd in smv_module.elements
        if isinstance(vd, smv.VarDeclaration)
        for (var_name, var_type) in vd.var_list
        if isinstance(var_type, smv.ModuleType)
    ]:
        module_name = var_type.module_name
        parameters = var_type.parameters
        for i, param in enumerate(parameters):
            # print(f"found parameter {param}")
            if isinstance(param, smv.ModuleAccess):
                module = param.module
                elem = param.element
                # if isinstance(module, nuxmv.ModuleAccess):
                #     module_to_check = module.element
                # else:
                #     module_to_check = module.ident

                mod_typ = context.vars[smv_module.name][module.ident]
                mod_typ = cast(smv.ModuleType, mod_typ)
                source_module = mod_typ.module_name

                if (
                    elem in context.defs[source_module]
                ):  # if the module access refers to a def'd element, specialize it and construct expr
                    translate_expr(
                        context.defs[source_module][elem],
                        context,
                        expr_map,
                        in_let_expr=False,
                        module=context.modules[module_name],
                    )
                    defn = expr_map[context.defs[source_module][elem]]
                    sdefn = specialize_vars_in_expr(to_moxi_ident(var_name.ident), defn)
                    init_expr = moxi.Apply.Eq(
                        [
                            context.module_locals[var_name.ident][i],
                            sdefn,
                        ]
                    )
                    inv_list.append(init_expr)
                else:
                    translate_expr(
                        param,
                        context,
                        expr_map,
                        in_let_expr=False,
                        module=smv_module,
                    )
                    init_expr = moxi.Apply.Eq(
                        [
                            context.module_locals[var_name.ident][i],
                            expr_map[param],
                        ]
                    )
                    inv_list.append(init_expr)
            else:  # Not a module access
                translate_expr(
                    param,
                    context,
                    expr_map,
                    in_let_expr=False,
                    module=smv_module,
                )
                init_expr = moxi.Apply.Eq(
                    [
                        context.module_locals[var_name.ident][i],
                        expr_map[param],
                    ]
                )
                inv_list.append(init_expr)

    # print("inv - done")
    return (
        moxi.conjoin_list(inv_list) if len(inv_list) > 0 else moxi.Constant.Bool(True)
    )


def gather_subsystems(
    smv_module: smv.ModuleDeclaration, smv_context: smv.Context
) -> dict[str, tuple[str, list[str]]]:
    """
    Subsystems in SMV are declared same as other variables, in the VAR section.
    ```   MODULE foo
          VAR
              x : integer; y : boolean;
              bar : module_bar(x, y); --- SUBMODULE!
    ```

    As such, skim through all smv.VarDeclarations (VAR sections) and if any of the variables
    have smv.ModuleType, register them and their parameters into the returned subsystems dict.
    """
    subsystems: dict[str, tuple[str, list[str]]] = {}

    for var_name, smv_var_type in [
        (var_name, smv_var_type)
        for e in smv_module.elements
        if isinstance(e, smv.VarDeclaration)
        for var_name, smv_var_type in e.var_list
        if isinstance(smv_var_type, smv.ModuleType)
    ]:
        subsystems[to_moxi_ident(var_name.ident)] = (
            smv_var_type.module_name,
            list(
                map(
                    lambda x: x.symbol,
                    smv_context.module_locals[to_moxi_ident(var_name.ident)],
                )
            ),
        )

    return subsystems


def gather_fairness(
    smv_module: smv.ModuleDeclaration,
    context: smv.Context,
    expr_map: dict[smv.Expr, moxi.Term],
) -> dict[str, moxi.Term]:
    """
    Return the negation of the translation of the FAIRNESS/JUSTICE formula.
    Moreover, assign a name, "fair_X", by which this property will be referred to in the CheckSystem query.
    """
    fairness_dict: dict[str, moxi.Term] = {}
    spec_num = 1
    for fairness_decl in [
        e
        for e in smv_module.elements
        if (
            isinstance(e, smv.FairnessDeclaration)
            or isinstance(e, smv.JusticeDeclaration)
        )
    ]:
        smv_expr = fairness_decl.formula
        translate_expr(
            smv_expr, context, expr_map, in_let_expr=False, module=smv_module
        )
        fairness_dict[f"fair_{spec_num}"] = cast(
            moxi.Term,
            moxi.Apply(
                moxi.Sort.Bool(), moxi.Identifier("not", []), [expr_map[smv_expr]]
            ),
        )
        spec_num += 1
    return fairness_dict


def gather_invarspecs(
    smv_module: smv.ModuleDeclaration,
    context: smv.Context,
    expr_map: dict[smv.Expr, moxi.Term],
) -> dict[str, moxi.Term]:
    """
    Return the negation of the translation of the INVARSPEC formula.
    Moreover, assign a name, "rch_X", by which this property will be referred to in the CheckSystem query.
    """
    invarspec_dict: dict[str, moxi.Term] = {}

    spec_num = 1
    for invarspec_decl in [
        e for e in smv_module.elements if isinstance(e, smv.InvarspecDeclaration)
    ]:
        smv_expr = invarspec_decl.formula
        translate_expr(
            smv_expr, context, expr_map, in_let_expr=False, module=smv_module
        )

        invarspec_dict[f"rch_{spec_num}"] = cast(
            moxi.Term,
            moxi.Apply(
                moxi.Sort.Bool(), moxi.Identifier("not", []), [expr_map[smv_expr]]
            ),
        )

        spec_num += 1

    return invarspec_dict


def gather_justice(
    smv_module: smv.ModuleDeclaration,
    context: smv.Context,
    expr_map: dict[smv.Expr, moxi.Term],
) -> dict[str, moxi.Term]:
    justice_dict: dict[str, moxi.Term] = {}

    spec_num = 1
    for justice_decl in [
        e for e in smv_module.elements if isinstance(e, smv.JusticeDeclaration)
    ]:
        smv_expr = justice_decl.formula
        translate_expr(
            smv_expr, context, expr_map, in_let_expr=False, module=smv_module
        )

        justice_dict[f"fair_{spec_num}"] = expr_map[smv_expr]

        spec_num += 1

    return justice_dict


def gather_pandaspecs(
    smv_module: smv.ModuleDeclaration,
    context: smv.Context,
    expr_map: dict[smv.Expr, moxi.Term],
) -> dict[str, moxi.Term]:
    pandaspec_dict: dict[str, moxi.Term] = {}

    spec_num = 1
    for pandaspec_decl in [
        e for e in smv_module.elements if isinstance(e, smv.PandaSpecDeclaration)
    ]:
        smv_expr = pandaspec_decl.formula
        translate_expr(
            smv_expr, context, expr_map, in_let_expr=False, module=smv_module
        )

        pandaspec_dict[f"panda_{spec_num}"] = expr_map[smv_expr]

        spec_num += 1

    return pandaspec_dict


def translate_module(
    smv_module: smv.ModuleDeclaration, context: smv.Context
) -> list[moxi.Command]:
    """
    Modules are translated by sweeps over the SMV spec.
    In particular, the sweeps are responsible for gathering system definitions comprising MoXI's DefineSystem
     - input variables via gather_input()
     - output variables via gather_output()
     - local variables via gather_local()
     - initial constraints via gather_init()
     - transition constraints via gather_trans()
     - invariant constraints via gather_inv()
     - subsystem instantiations via gather_subsystems()

    A second set of sweeps are responsible for the system queries comprising MoXI's CheckSystem:
     - fairness properties via gather_fairness()
     - reachable queries via gather_invarspecs()

    The function necessarily returns one DefineSystem command with an optional CheckSystem command.
    """
    commands: list[moxi.Command] = []

    module_name = to_moxi_ident(smv_module.name)

    log.debug(2, f"Translating module '{module_name}'", FILE_NAME)

    # log.debug(2, "Translating enums", FILE_NAME)
    # enums = gather_enums(smv_module, context)

    log.debug(2, "Translating input variables", FILE_NAME)
    input = gather_input(smv_module, context)

    log.debug(2, "Translating output variables", FILE_NAME)
    output = gather_output(smv_module, context)

    log.debug(2, "Translating local variables", FILE_NAME)
    local = gather_local(smv_module, context)

    log.debug(2, "Translating initialization constraints", FILE_NAME)
    expr_map = {}
    init = gather_init(smv_module, context, expr_map)

    log.debug(2, "Translating transition relation", FILE_NAME)
    trans = gather_trans(smv_module, context, expr_map)

    log.debug(2, "Translating invariant constraints", FILE_NAME)
    inv = gather_inv(smv_module, context, expr_map)

    subsystems = gather_subsystems(smv_module, context)

    commands.append(
        moxi.DefineSystem(
            symbol=smv_module.name,
            input=input,
            output=output,
            local=local,
            init=init,
            trans=trans,
            inv=inv,
            subsystems=subsystems,
        )
    )

    # In nuXmv, INVARSPEC properties do not consider fariness constraints (p41 of user manual). To
    # account for this with encoded LTLSPECs, we use special __PANDASPEC__s to denote an INVARSPEC
    # that respects JUSTICE constraints.

    reachable: dict[str, moxi.Term] = gather_invarspecs(smv_module, context, expr_map)
    justice: dict[str, moxi.Term] = gather_justice(smv_module, context, expr_map)
    panda: dict[str, moxi.Term] = gather_pandaspecs(smv_module, context, expr_map)

    if len(reachable) == 0 and len(panda) == 0:
        check_system: list[moxi.Command] = []
    else:
        check_system: list[moxi.Command] = [
            moxi.CheckSystem(
                symbol=smv_module.name,
                input=input,
                output=output,
                local=local,
                assumption={},
                fairness=justice,
                reachable=reachable | panda,
                current={},
                query={f"qry_{r}": [r] for r in reachable.keys()}
                | {f"qry_{p}": [p] + list(justice.keys()) for p in panda.keys()},
                queries=[],
            )
        ]

    commands += check_system

    # commands
    # consts: list[moxi.Command] = gather_consts(smv_module)

    return commands


def infer_logic(context: smv.Context) -> Optional[moxi.SetLogic]:
    """
    Infers SMT logic based on sorts of occurring variables - if a single Int variable is found, set to QF_NIA, otherwise QF_ABV
    """
    if not any(
        [context.has_arrays, context.has_ufs, context.has_bitvecs, context.has_integers]
    ):
        return None

    logic = "QF_"
    if context.has_arrays:
        logic += "A"
    if context.has_ufs:
        logic += "UF"
    if context.has_bitvecs:
        logic += "BV"
    if context.has_integers:
        logic += "NIA"

    return moxi.SetLogic(logic)


def translate(
    filename: str, smv_program: smv.Program, logic: Optional[str]
) -> Optional[moxi.Program]:
    """
    - Performs type-checking on input smv_program
    - Modules translated in backwards order (depending on what shows up in the specification)
    - Mines any declare-enum-sort/declare-fun commands depending on what's found in their respective contexts (context.enums, context.functions)
    - Infers corresponding SMT logics depending on what variable sorts show up in the program (integers automatically set to QF_LIA, otherwise work with QF_ABV)
    """
    if not smv_program.main:
        log.error("No module 'main', cannot translate.", FILE_NAME)
        return None

    log.debug(1, "Type checking", FILE_NAME)
    context = smv.Context(filename, smv_program.modules)
    well_typed = smv.type_check_module(smv_program.main, context)

    if not well_typed:
        log.error("Failed type checking", FILE_NAME)
        return None

    commands: list[moxi.Command] = []

    for smv_module in smv_program.modules:
        panda.handle_ltlspecs(smv_module, context)
        smv.type_check_module(smv_module, context)
        # ltlspec_modules = panda.get_ltlspec_modules(smv_module, context)
        # if ltlspec_modules:
        #     smv.type_check_module(smv_module, context)

    commands += [
        moxi.DeclareEnumSort(symbol, [str(s) for s in enum.summands])
        for symbol, enum in context.enums.items()
        if enum.is_symbolic()
    ]

    commands += [
        moxi.DeclareFun(
            symbol=symbol,
            inputs=[translate_type(t, context) for t in type[0]],
            output=translate_type(type[1], context),
        )
        for symbol, type in context.functions.items()
    ]

    for module in context.get_module_dep_order(smv_program.main):
        commands += translate_module(smv_module=module, context=context)

    if logic:
        the_logic = moxi.SetLogic(logic)
    else:
        the_logic = infer_logic(context)

    if the_logic:
        commands = [the_logic] + commands

    return moxi.Program(commands=commands)


def translate_file(
    input_path: pathlib.Path,
    output_path: pathlib.Path,
    do_cpp: bool,
    logic: Optional[str],
) -> int:
    """Parses, type checks, translates, and writes the translation result of `input_path` to `output_path`. Runs C preprocessor if `do_cpp` is True. Returns 0 on success, 1 otherwise."""
    if not input_path.is_file():
        log.error(f"'{input_path}' is not a valid file.", FILE_NAME)
        return 1

    if output_path.exists():
        log.error(f"Output path '{output_path}' already exists.", FILE_NAME)
        return 1

    log.debug(1, "Parsing", FILE_NAME)
    parse_tree = parse_smv.parse(input_path, do_cpp)
    if not parse_tree:
        log.debug(1, f"Failed parsing specification {input_path}", FILE_NAME)
        return 1

    log.debug(1, "Translating", FILE_NAME)
    result = translate(input_path.name, parse_tree, logic)
    if not result:
        log.debug(1, f"Failed translating specification {input_path}", FILE_NAME)
        return 1

    if output_path.exists():
        log.error(f"File already exists '{output_path}'", FILE_NAME)
        return 1

    log.debug(1, f"Writing output to {output_path}", FILE_NAME)

    with open(str(output_path), "w") as f:
        f.write(str(result))
        log.debug(1, f"Wrote output to {output_path}", FILE_NAME)

    return 0
