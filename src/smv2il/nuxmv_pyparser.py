from collections import OrderedDict
from functools import reduce
import argparse

from pyparsing import *

if __package__ == "":
    from model import *
else:
    from .model import *
    from .model import Expression

ParserElement.enable_packrat()


"""
This file prototypes a parser from (a subset of) nuXmv into the IL.

DISCLAIMER/ACKNOWLEDGEMENT: 
Many parts of the parser (and model.py/utils.py) were taken from the PyNuSMV project 
(https://github.com/sbusard/pynusmv)

There're a lot of unnecessary artifacts in this file and the dependent 
model.py/utils.py that we could get rid of once the main translation is complete.

TODO: Stress-testing (on new examples located in examples/nuxmv-exmaples)
TODO: Parsing specifications
"""


reserved = (Keyword("AG")
            | Keyword("AF")
            | Keyword("AX")
            | Keyword("EG")
            | Keyword("EF")
            | Keyword("EX"))

def _reduce_list_to_expr(list_):
    _otc = {"*": Mult, "/": Div, "mod": Mod, "+": Add, "-": Sub,
            "<<": LShift, ">>": RShift,
            "=": Equal, "!=": NotEqual, "<": Lt, ">": Gt, "<=": Le, ">=": Ge,
            "|": Or, "xor": Xor, "xnor": Xnor}

    res = list_[0]
    for operator, token in zip(list_[1::2], list_[2::2]):
        res = _otc[operator](res, token)
    return res


# Identifiers
identifier = ~reserved + Word(alphas + "_$", alphanums + "_$#-")
identifier.setParseAction(lambda s, l, t: Identifier(t[0]))

simple_expression = Forward()

# Variable and DEFINE identifiers
_cip = Forward()
_cip <<= Optional("." + Literal("self") + _cip
                  | "." + identifier + _cip
                  | "." + Word(nums) + _cip
                  | "[" + simple_expression + "]" + _cip)
complex_identifier = Forward()
complex_identifier <<= ((FollowedBy("self") + Literal("self") + _cip)
                      | (identifier + _cip)
                      | Suppress('"') + complex_identifier + Suppress('"'))


def _handle_ci(tokens):
    def _handle_id(token):
        if (str(token) == "self"):
            return Self()
        else:
            return token

    if len(tokens) <= 1:
        return _handle_id(tokens[0])
    elif tokens[1] == ".":
        return Dot(_handle_id(tokens[0]), _handle_ci(tokens[2:]))
    else:  # tokens[1] == "["
        return _handle_ci([ArrayAccess(_handle_id(tokens[0]), tokens[2])] +
                          tokens[4:])

complex_identifier.setParseAction(lambda s, l, t: _handle_ci(t))

_define_identifier = complex_identifier
_variable_identifier = complex_identifier


# Integer numbers
_integer_number = Combine(Optional("-") + Word(nums))
_integer_number.setParseAction(lambda s, l, t: int(t[0]))

# Constants
_boolean_constant = oneOf("TRUE FALSE")
_boolean_constant.setParseAction(lambda s, l, t:
                                 Falseexp() if t[0] == "FALSE" else Trueexp())

_integer_constant = _integer_number
_symbolic_constant = identifier
_range_constant = _integer_number + Suppress("..") + _integer_number
_range_constant.setParseAction(lambda s, l, t: RangeConst(t[0], t[1]))

_word_sign_specifier = oneOf("u s")
_word_base = oneOf("b B o O d D h H")
_word_width = Word(nums)
_word_value = Word("0123456789abcdefABCDEF", "0123456789abcdefABCDEF_")
_word_constant = Combine(Literal("0") + Optional(_word_sign_specifier)
                         + _word_base + Optional(_word_width) + "_"
                         + _word_value)
_word_constant.setParseAction(lambda s, l, t: NumberWord(t[0]))

_string_constant = Suppress('"') + Word(alphanums + "_!:;@#$%^&*(),.`|\\") + Suppress('"')

constant = (_word_constant
            # | _range_constant
            | _integer_constant | _boolean_constant | _symbolic_constant)

# Basic expressions
_basic_expr = Forward()
_conversion = (Literal("word1") + Suppress("(") + _basic_expr + Suppress(")")
               | Literal("bool") + Suppress("(") + _basic_expr + Suppress(")")
               | Literal("toint") + Suppress("(") + _basic_expr + Suppress(")")
               | Literal("signed") + Suppress("(") + _basic_expr
               + Suppress(")")
               | Literal("unsigned") + Suppress("(") + _basic_expr
               + Suppress(")"))
_conversion.setParseAction(lambda s, l, t: Conversion(t[0], t[1]))

_word_function = (Literal("extend") + Suppress("(") + _basic_expr + ","
                  + _basic_expr + Suppress(")")
                  | Literal("resize") + Suppress("(") + _basic_expr + ","
                  + _basic_expr + Suppress(")"))
_word_function.setParseAction(lambda s, l, t: WordFunction(t[0], t[1], t[2]))

_count = (Literal("count") + Suppress("(") + delimitedList(_basic_expr)
          + Suppress(")"))
_count.setParseAction(lambda s, l, t: Count(t[1]))

_next = Literal("next") + Suppress("(") + _basic_expr + Suppress(")")
_next.setParseAction(lambda s, l, t: Next(t[1]))

_case_case = _basic_expr + Suppress(":") + _basic_expr + Suppress(";")
_case_body = OneOrMore(_case_case)
_case_body.setParseAction(lambda s, l, t: OrderedDict(zip(t[::2], t[1::2])))
_case = Suppress("case") + _case_body + Suppress("esac")
_case.setParseAction(lambda s, l, t: Case(t[0]))

_base = (complex_identifier ^
         (_conversion
          | _word_function
          | _count
          | _next
          | Suppress("(") + _basic_expr + Suppress(")")
          | _case
          | constant))

_ap = Forward()
_array_subscript = Group(Suppress("[") + _basic_expr + Suppress("]"))

_word_bit_selection = Group(Suppress("[") + _basic_expr + Suppress(":")
                            + _basic_expr + Suppress("]"))

_ap <<= Optional(_array_subscript + _ap | _word_bit_selection + _ap)
_array = _base + _ap


def _handle_array(tokens):
    if len(tokens) <= 1:
        return tokens[0]
    elif len(tokens[1]) == 1:
        return _handle_array([Subscript(tokens[0], tokens[1][0])] + tokens[2:])
    else:  # len(tokens[1]) == 2
        return _handle_array([BitSelection(tokens[0], tokens[1][0],
                                           tokens[1][1])] +
                             tokens[2:])


_array.setParseAction(lambda s, l, t: _handle_array(t))

_not = ZeroOrMore("!") + _array
_not.setParseAction(lambda s, l, t: reduce(lambda e, n: Not(e), t[:-1], t[-1]))

_concat = _not + ZeroOrMore(Suppress("::") + _not)
_concat.setParseAction(lambda s, l, t: reduce(lambda e, n: Concat(e, n),
                                              t[0:1] + t[2::2]))

_minus = ZeroOrMore("-") + _concat
_minus.setParseAction(lambda s, l, t: reduce(lambda e, n: Minus(e),
                                             t[:-1], t[-1]))

_mult = _minus + ZeroOrMore(oneOf("* / mod") + _minus)
_mult.setParseAction(lambda s, l, t: _reduce_list_to_expr(t))

_add = _mult + ZeroOrMore(oneOf("+ -") + _mult)
_add.setParseAction(lambda s, l, t: _reduce_list_to_expr(t))

_shift = _add + ZeroOrMore(oneOf("<< >>") + _add)
_shift.setParseAction(lambda s, l, t: _reduce_list_to_expr(t))

_set_set = Suppress("{") + delimitedList(_basic_expr) + Suppress("}")
_set_set.setParseAction(lambda s, l, t: Set(t))
_set = (_range_constant | _shift | _set_set)

_union = _set + ZeroOrMore("union" + _set)
_union.setParseAction(lambda s, l, t: reduce(lambda e, n: Union(e, n),
                                             t[0:1] + t[2::2]))

_in = _union + ZeroOrMore("in" + _union)
_in.setParseAction(lambda s, l, t: reduce(lambda e, n: In(e, n),
                                          t[0:1] + t[2::2]))

_comparison = _in + ZeroOrMore(oneOf("= != < > <= >=") + _in)
_comparison.setParseAction(lambda s, l, t: _reduce_list_to_expr(t))

_and = _comparison + ZeroOrMore("&" + _comparison)
_and.setParseAction(lambda s, l, t: reduce(lambda e, n: And(e, n),
                                           t[0:1] + t[2::2]))

_or = _and + ZeroOrMore(oneOf("| xor xnor") + _and)
_or.setParseAction(lambda s, l, t: _reduce_list_to_expr(t))

_ite = Forward()
_ite <<= _or + Optional("?" + _ite + ":" + _ite)
_ite.setParseAction(lambda s, l, t:
                    t[0] if len(t) <= 1 else Ite(t[0], t[2], t[4]))

_iff = _ite + ZeroOrMore("<->" + _ite)
_iff.setParseAction(lambda s, l, t: reduce(lambda e, n: Iff(e, n),
                                           t[0:1] + t[2::2]))

_implies = Forward()
_implies <<= _iff + ZeroOrMore("->" + _implies)
_implies.setParseAction(lambda s, l, t: reduce(lambda e, n: Implies(n, e),
                                               t[0:1] + t[2::2]))

_basic_expr <<= _implies

simple_expression <<= _basic_expr
next_expression = _basic_expr

# Type specifier
_simple_type_specifier = Forward()

_boolean_type = Literal("boolean")
_boolean_type.setParseAction(lambda s, l, t: Boolean())

_integer_type = Literal("integer")
_integer_type.setParseAction(lambda s, l, t: Integer())

_word_type = (Optional(Literal("unsigned") | Literal("signed"))
              + Literal("word") + Suppress("[") + _basic_expr + Suppress("]"))
_word_type.setParseAction(lambda s, l, t: MWord(t[1]) if t[0] == "word"
                          else MWord(t[2], sign=t[0]))

_enum_type = (Suppress("{")
              + delimitedList(_integer_number | _symbolic_constant)
              + Suppress("}"))
_enum_type.setParseAction(lambda s, l, t: Scalar(t))

_range_type = _shift + Suppress("..") + _shift
_range_type.setParseAction(lambda s, l, t: Range(t[0], t[1]))

_array_type = (Suppress("array") + _shift + Suppress("..") + _shift
               + Suppress("of") + _simple_type_specifier)
_array_type.setParseAction(lambda s, l, t: Array(t[0], t[1], t[2]))

_simple_type_specifier <<= (_boolean_type
                            | _word_type
                            | _enum_type
                            | _array_type
                            | _range_type
                            | _integer_type)

_module_type_specifier = (identifier
                          + Optional(Suppress("(")
                                     +
                                     Optional(delimitedList(simple_expression))
                                     + Suppress(")")))
_module_type_specifier.setParseAction(
    lambda s, l, t: Modtype(t[0], t[1:]))

type_identifier = _simple_type_specifier | _module_type_specifier

# Variables
_var_declaration1 = complex_identifier + Suppress(":") + type_identifier + Suppress(";")
_var_declaration2 = Suppress('"') + complex_identifier + Suppress('"') + Suppress(":") + type_identifier + Suppress(";")
_var_declaration = _var_declaration1 | _var_declaration2

_var_section_body = OneOrMore(_var_declaration)
_var_section_body.setParseAction(lambda s, l, t:
                                 OrderedDict(zip(t[::2], t[1::2])))
var_section = Suppress("VAR") + _var_section_body
var_section.setParseAction(lambda s, l, t: Variables(t[0]))

_ivar_declaration1 = (complex_identifier + Suppress(":") + _simple_type_specifier
                     + Suppress(";"))

_ivar_declaration2 = (Suppress('"') + complex_identifier + Suppress('"') + Suppress(":") + _simple_type_specifier
                     + Suppress(";"))
_ivar_declaration = _ivar_declaration1 | _ivar_declaration2

_ivar_section_body = OneOrMore(_ivar_declaration)
_ivar_section_body.setParseAction(lambda s, l, t:
                                  OrderedDict(zip(t[::2], t[1::2])))
ivar_section = Suppress("IVAR") + _ivar_section_body
ivar_section.setParseAction(lambda s, l, t: InputVariables(t[0]))

_frozenvar_declaration = (identifier + Suppress(":") + _simple_type_specifier
                          + Suppress(";"))
_frozenvar_section_body = OneOrMore(_frozenvar_declaration)
_frozenvar_section_body.setParseAction(lambda s, l, t:
                                       OrderedDict(zip(t[::2], t[1::2])))
frozenvar_section = Suppress("FROZENVAR") + _frozenvar_section_body
frozenvar_section.setParseAction(lambda s, l, t: FrozenVariables(t[0]))

# DEFINE and CONSTANTS
_array_expression = Forward()
_array_expression <<= ( Suppress("[") + Group(delimitedList(next_expression))
                        + Suppress("]")
                      | Suppress("[") + Group(delimitedList(_array_expression))
                        + Suppress("]"))
_define = _array_expression | next_expression
_define_declaration = (complex_identifier + Suppress(":=") + _define + Suppress(";"))

def _handle_define_body(s, l, t):
    b = OrderedDict()
    for identifier, body in zip(t[::2], t[1::2]):
        if not isinstance(body, Expression):
            body = ArrayExpr(body)
        b[identifier] = body
    return b
_define_section_body = OneOrMore(_define_declaration)
_define_section_body.setParseAction(_handle_define_body)
define_section = Suppress("DEFINE") + _define_section_body
define_section.setParseAction(lambda s, l, t: Defines(t[0]))

_constants_section_body = delimitedList(identifier) + Suppress(";")
_constants_section_body.setParseAction(lambda s, l, t: list(t))
constants_section = Suppress("CONSTANTS") + _constants_section_body
constants_section.setParseAction(lambda s, l, t: Constants(list(t)))

# ASSIGN, TRANS, INIT, INVAR, FAIRNESS
_assign_identifier = (Literal("init") + Suppress("(") + complex_identifier
                      + Suppress(")")
                      | Literal("next") + Suppress("(") + complex_identifier
                      + Suppress(")")
                      | complex_identifier)
_assign_identifier.setParseAction(lambda s, l, t:
                                  Smallinit(t[1]) if str(t[0]) == "init"
                                  else Next(t[1]) if str(t[0]) == "next"
                                  else t[0])
_assign = (_assign_identifier + Suppress(":=") + simple_expression
           + Suppress(";"))
_assign_constraint_body = OneOrMore(_assign)
_assign_constraint_body.setParseAction(lambda s, l, t:
                                       OrderedDict(zip(t[::2], t[1::2])))
assign_constraint = Suppress("ASSIGN") + _assign_constraint_body
assign_constraint.setParseAction(lambda s, l, t: Assigns(t[0]))

_trans_constraint_body = next_expression + Optional(Suppress(";"))
_trans_constraint_body.setParseAction(lambda s, l, t: list(t))
trans_constraint = Suppress("TRANS") + _trans_constraint_body
trans_constraint.setParseAction(lambda s, l, t: Trans(list(t)))

_init_constraint_body = simple_expression + Optional(Suppress(";"))
# _init_constraint_body.setParseAction(lambda s, l, t: list(t))
init_constraint = Suppress("INIT") + _init_constraint_body
init_constraint.setParseAction(lambda s, l, t: Init(list(t)))

_invar_constraint_body = simple_expression + Optional(Suppress(";"))
_invar_constraint_body.setParseAction(lambda s, l, t: list(t))
invar_constraint = Suppress("INVAR") + _invar_constraint_body
invar_constraint.setParseAction(lambda s, l, t: Invar(list(t)))

_invarspec_constraint_body = simple_expression + Optional(Suppress(";"))
_invarspec_constraint_body.setParseAction(lambda s, l, t: list(t))
invarspec_constraint = Suppress("INVARSPEC") + _invarspec_constraint_body
invarspec_constraint.setParseAction(lambda s, l, t: InvarSpec(list(t)))

_spec_constraint_body = simple_expression + Optional(Suppress(";"))
_spec_constraint_body.setParseAction(lambda s, l, t: list(t))
spec_constraint = Suppress("SPEC") + _invarspec_constraint_body
spec_constraint.setParseAction(lambda s, l, t: Spec(list(t)))


_fairness_constraint_body = simple_expression + Optional(Suppress(";"))
_fairness_constraint_body.setParseAction(lambda s, l, t: list(t))
fairness_constraint = Suppress("FAIRNESS") + _fairness_constraint_body
fairness_constraint.setParseAction(lambda s, l, t: Fairness(list(t)))

_justice_constraint_body = simple_expression + Optional(Suppress(";"))
_justice_constraint_body.setParseAction(lambda s, l, t: list(t))
justice_constraint = Suppress("JUSTICE") + _justice_constraint_body
justice_constraint.setParseAction(lambda s, l, t: Justice(list(t)))

_compassion_constraint_body = (Suppress("(")
                               + simple_expression + Suppress(",")
                               + simple_expression + Suppress(")")
                               + Optional(Suppress(";")))
_compassion_constraint_body.setParseAction(lambda s, l, t: [t[0], t[1]])
compassion_constraint = Suppress("COMPASSION") + _compassion_constraint_body
compassion_constraint.setParseAction(lambda s, l, t: Compassion(list(t)))

# CTL --------------------------------------------------
# shouldn't have to deal with this
ctl_expr = Forward()

ctl_expr1 = Forward()
ctl_expr2 = Forward()

ctl_expr1 <<= infix_notation(
    _basic_expr , # ctl_expr
    [
        # ("!", 1, OpAssoc.RIGHT),
        (one_of("! AG AF AX EG EF EX"), 1, OpAssoc.RIGHT),
        # (AG, 1, OpAssoc.RIGHT),
        # (AF, 1, OpAssoc.RIGHT),
        # (AX, 1, OpAssoc.RIGHT),
        # (EG, 1, OpAssoc.RIGHT),
        # (EF, 1, OpAssoc.RIGHT),
        # (EX, 1, OpAssoc.RIGHT),
        (one_of("& |"), 2, OpAssoc.LEFT),
        (one_of("-> <->"), 2, OpAssoc.RIGHT),
        (one_of("xor xnor"), 2, OpAssoc.LEFT),
    ],
    lpar="(",
    rpar=")"
)

ctl_expr2 <<= one_of("E A") + Suppress("[") + ctl_expr + Suppress("U") + ctl_expr + Suppress("]")

ctl_expr <<=  ctl_expr2 | ctl_expr1

# ctl_specification = Suppress("SPEC") + ctl_expr + Optional(Suppress(";"))
ctl_specification = (Suppress("CTLSPEC") + ctl_expr
                     | Suppress("SPEC") + ctl_expr + Optional(Suppress(";"))
                     | Suppress("CTLSPEC NAME") + identifier + Suppress(":=") + ctl_expr + Optional(Suppress(";"))
                     | Suppress("SPEC NAME") + identifier + Suppress(":=") + ctl_expr + Optional(Suppress(";")))

# LTL --------------------------------------------------
# TODO: test this!

ltl_expr = Forward()

bound1 = Suppress("[") + _integer_number + Suppress(",") + _integer_number + Suppress("]")
bound1.setParseAction(lambda s, l, t: Bound(t[0], t[1]))
bound2 = Suppress("[") + _integer_number + Suppress(",") + Suppress("+oo)")
bound2.setParseAction(lambda s, l, t: Bound(t[0], Inf()))
bound = (bound1
         | bound2)

comp_ltl_expr = bound + ltl_expr

ltl_expr = infix_notation (
    next_expression | ltl_expr | comp_ltl_expr,
    [
        ("!", 1, OpAssoc.RIGHT),
        (one_of("& |"), 2, OpAssoc.LEFT),
        (one_of("-> <->"), 2, OpAssoc.RIGHT),
        (one_of("xor xnor"), 2, OpAssoc.LEFT),
        ("X", 1, OpAssoc.RIGHT),
        ("G", 1, OpAssoc.RIGHT),
        ("F", 1, OpAssoc.RIGHT),
        (one_of("U V"), 2, OpAssoc.LEFT),
        ("Y", 1, OpAssoc.RIGHT),
        ("Z", 1, OpAssoc.RIGHT),
        ("H", 1, OpAssoc.RIGHT),
        ("O", 1, OpAssoc.RIGHT),
        (one_of("S T"), 2, OpAssoc.LEFT),
    ],
    lpar="(",
    rpar=")"
)

# ltl_expr = Forward()

# at_expr = Forward()
# at_expr = (next_expression
#            | ltl_expr
#            | at_expr + Suppress("at next") + at_expr
#            | at_expr + Suppress("@F~") + at_expr
#            | at_expr + Suppress("at last") + at_expr
#            | at_expr + Suppress("@O~") + at_expr)

# ltl_expr = (at_expr
#             | Suppress("(") + ltl_expr + Suppress(")")
#             | Suppress("!") + ltl_expr
#             | ltl_expr + Suppress("&") + ltl_expr)


ltl_specification = (Suppress("LTLSPEC") + ltl_expr
                    | Suppress("LTLSPEC NAME") + identifier + Suppress(":=") + ltl_expr + Optional(Suppress(";")))

# COMPUTE/RTCTL --------------------------------------------------
# shouldn't have to deal with this

rtctl_expr = Forward()
rtctl_expr = (ctl_expr
              | Keyword("EBF") + _range_constant + rtctl_expr
              | Keyword("ABF") + _range_constant + rtctl_expr
              | Keyword("EBG") + _range_constant + rtctl_expr
              | Keyword("EBG") + _range_constant + rtctl_expr
              | one_of("A E") + Suppress("[") + rtctl_expr + Suppress("BU") + _range_constant + rtctl_expr + Suppress("]"))

compute_expr = Forward()
compute_expr = one_of("MIN MAX") + Suppress("[") + rtctl_expr + Suppress(",") + rtctl_expr + Suppress("]")

compute_specification = (Suppress("COMPUTE") + compute_expr + Optional(Suppress(";"))
                         | Suppress("COMPUTE NAME") + identifier + Suppress(":=") + compute_expr + Optional(Suppress(";")))
compute_specification.setParseAction(lambda s, l, t: Compute(list(t)))


# Function declaration ---------------------------------

function_args_type_specifier = ZeroOrMore(_simple_type_specifier + Suppress("*")) + _simple_type_specifier
function_args_type_specifier.setParseAction(lambda s, l, t: Prod(t))
function_type_specifier = function_args_type_specifier + Suppress("->") + _simple_type_specifier
function_type_specifier.setParseAction(lambda s, l, t: FunType(t[0], t[1]))
function_declaration2 = identifier + Suppress(":") + function_type_specifier + Suppress(";")
function_declaration2.setParseAction(lambda s, l, t: FunDecl(name=t[0], type=t[1]))
function_list = OneOrMore(function_declaration2)
function_list.setParseAction(lambda s, l, t: list(t[0:]))
function_declaration = Suppress("FUN") + function_list
function_declaration.setParseAction(lambda s, l, t: FunctionDeclaration(t))

# Modules ----------------------------------------------
_module_element = (var_section
                   | ivar_section
                   | frozenvar_section
                   | define_section
                   | function_declaration
                   | constants_section
                   | assign_constraint
                   | trans_constraint
                   | init_constraint
                   | invarspec_constraint
                   | spec_constraint
                   | invar_constraint
                   | fairness_constraint
                   | justice_constraint
                   | compassion_constraint
                #    | ctl_specification
                   | ltl_specification
                   | compute_specification)

_module_args = (Suppress("(") + Optional(delimitedList(identifier)) +
                Suppress(")"))
module = (Suppress("MODULE") + identifier + Group(Optional(_module_args))
          + ZeroOrMore(_module_element))


counter = 0
def gensym(string):
    global counter
    counter += 1
    return (string + str(counter))

def _create_module(string, location, tokens):
    # from model import ModuleMetaClass, Module as ModuleClass

    name = tokens[0]
    args = tokens[1]
    namespace = OrderedDict()
    namespace["NAME"] = name
    namespace["ARGS"] = args
    for section in tokens[2:]:
        namespace[gensym(section.name)] = section.body

    return namespace
    # return ModuleMetaClass(str(name), (ModuleClass,), namespace)

module.setParseAction(_create_module)

start = OneOrMore(module)

# =========================================================


def parseAllString(parser, string):
    res = parser.parseString(string, parseAll=True)
    return res

def strip_comments(file):
    text = ""
    for line in file:
        stripped = line.split("--", 1)[0]
        text += stripped

    return text

def parse(file):
    string = strip_comments(file)
    return parseAllString(start, string)


def update(old, new):
    try:
        old.extend(new)
    except AttributeError:
        old.update(new)

# =========================================================

def main():
    # test()

    argparser = argparse.ArgumentParser(
                           prog='nuXmv/NuSMV pyparsing parser',
                           description='Parses a nuXmv/NuSMV (.smv) file using pyparsing'
     )

    argparser.add_argument('filename')

    args = argparser.parse_args()
    file = open(args.filename)

    string = strip_comments(file)

    parsed = parse(string)

    for p in parsed:
        print(p)


def test():
    string = """
    SPEC
    AG AF bit2.carry_out
    """

    print(spec_constraint.parseString(string, parseAll=True))


if __name__ == '__main__':
    main()