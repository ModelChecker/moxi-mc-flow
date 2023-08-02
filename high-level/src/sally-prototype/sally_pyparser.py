import argparse
from dataclasses import dataclass
import pprint
from typing import List, Tuple
from pyparsing import *
import rich


"""
This file prototypes a parser from Sally to the IL.

This parser should be mostly complete - passes all tests.

"""


def unwrap(elem):
    try:
        return elem.asList()
    except AttributeError:
        return elem

# ============= MISC CLASSES ================

@dataclass
class Expression:
    pass

@dataclass
class Binop:
    op: str
    lhs: Expression
    rhs: Expression

@dataclass
class Unop:
    op: str
    operand: Expression

@dataclass
class Add:
    args: List[Expression]

@dataclass
class Mult:
    args: List[Expression]


@dataclass(frozen=True)
class And:
    args: List[Expression]

@dataclass
class Or:
    args: List[Expression]

@dataclass
class Not:
    expr: Expression


@dataclass
class Let:
    vars: List[Tuple[str, Expression]]
    expr: Expression

@dataclass
class Cond:
    cases: List[Tuple[Expression, Expression]]


@dataclass
class Ite:
    cond: Expression
    t: Expression
    e: Expression


# ============= MAIN CLASSES ================

@dataclass
class DefineConstant:
    name: str
    val: str

@dataclass
class DefineStateType:
    name: str
    inputs: List[Tuple[str, str]]
    vars: List[Tuple[str, str]]

@dataclass
class DefineStates:
    name: str
    state_type: str
    pred: Expression

@dataclass
class DefineTransition:
    name: str
    state_type: str
    pred: Expression

@dataclass
class DefineTransitionSystem:
    name: str
    state_type: str
    initial_states: Expression
    transition: Expression

@dataclass
class Assume:
    system: str
    assumption: Expression

@dataclass
class Query:
    name: str
    query: Expression

@dataclass
class Interpolate:
    pass

@dataclass
class Generalize:
    pass

@dataclass
class Checksat:
    pass

# ============= PARSER ================

LPAREN = Suppress("(")
RPAREN = Suppress(")")

identchars = "_.!'"
Ident = ~Keyword("and", ident_chars=identchars) + \
    ~Keyword("or", ident_chars=identchars) + \
    ~Keyword("let", ident_chars=identchars) + \
    ~Keyword("not", ident_chars=identchars) + \
    ~Keyword("cond", ident_chars=identchars) + \
    ~Keyword("ite", ident_chars=identchars) + \
    Word(alphas + '_', alphanums + identchars)

Integer = Word(nums)

expr = Forward()
op = oneOf("+ - * / >= <= > < = and or")

basic = Integer | Ident
subexpr = Forward()


add = Suppress("+") + OneOrMore(subexpr)
add.setParseAction(lambda s, l, t: Add(unwrap(t)))
# add.setParseAction(lambda s, l, t: Binop(op="+", lhs=unwrap(t[0]), rhs=unwrap(t[1])))

subtract = Suppress("-") + subexpr + subexpr
subtract.setParseAction(lambda s, l, t: Binop(op="-", lhs=unwrap(t[0]), rhs=unwrap(t[1])))

minus = Suppress("-") + subexpr
minus.setParseAction(lambda s, l, t: Unop(op="-", operand=t[0]))

multiply = Suppress("*") + OneOrMore(subexpr)
multiply.setParseAction(lambda s, l, t: Mult(unwrap(t)))
# multiply.setParseAction(lambda s, l, t: Binop(op="*", lhs=unwrap(t[0]), rhs=unwrap(t[1])))

divide = Suppress("/") + subexpr + subexpr
divide.setParseAction(lambda s, l, t: Binop(op="/", lhs=unwrap(t[0]), rhs=unwrap(t[1])))

leq = Suppress("<=") + subexpr + subexpr
leq.setParseAction(lambda s, l, t: Binop(op="<=", lhs=unwrap(t[0]), rhs=unwrap(t[1])))

lt = Suppress("<") + subexpr + subexpr
lt.setParseAction(lambda s, l, t: Binop(op="<", lhs=unwrap(t[0]), rhs=unwrap(t[1])))

geq = Suppress(">=") + subexpr + subexpr
geq.setParseAction(lambda s, l, t: Binop(op=">=", lhs=unwrap(t[0]), rhs=unwrap(t[1])))

gt = Suppress(">") + subexpr + subexpr
gt.setParseAction(lambda s, l, t: Binop(op=">", lhs=unwrap(t[0]), rhs=unwrap(t[1])))

eq = Suppress("=") + subexpr + subexpr
eq.setParseAction(lambda s, l, t: Binop(op="=", lhs=unwrap(t[0]), rhs=unwrap(t[1])))

neq = Suppress("/=") + subexpr + subexpr
neq.setParseAction(lambda s, l, t: Binop(op="/=", lhs=unwrap(t[0]), rhs=unwrap(t[1])))

_and = Suppress("and") + OneOrMore(subexpr)
_and.setParseAction(lambda s, l, t: And(unwrap(t)))


# _or = Suppress(Literal("or")) + subexpr + subexpr
# _or.setParseAction(lambda s, l, t: Binop(op="or", lhs=unwrap(t[0]), rhs=unwrap(t[1])))

_or = Suppress("or") + OneOrMore(subexpr)
_or.setParseAction(lambda s, l, t: Or(unwrap(t)))


_not = Suppress(Literal("not")) + subexpr
_not.setParseAction(lambda s, l, t: Not(expr=t[0]))



letvars = LPAREN + Ident + subexpr + RPAREN

def create_letvars(list):
    assert(len(list) % 2 == 0)
    letvars = []
    i = 0
    while i < len(list):
        name = list[i]
        val = list[i + 1]
        letvars.append((name, val))
        i += 2

    return letvars


_let = Suppress(Literal("let")) + LPAREN + OneOrMore(letvars) + RPAREN + subexpr
_let.setParseAction(lambda s, l, t: Let(vars=create_letvars(t[:-1]), expr=t[-1]))


condpairs = LPAREN + subexpr + subexpr + RPAREN

def create_condpairs(list):
    assert(len(list) % 2 == 0)
    condpairs = []
    i = 0
    while i < len(list):
        name = list[i]
        val = list[i + 1]
        condpairs.append((name, val))
        i += 2

    return condpairs

_cond = Suppress(Keyword("cond")) + OneOrMore(condpairs)
_cond.setParseAction(lambda s, l, t: Cond(cases=create_condpairs(t)))

_ite = Suppress(Keyword("ite")) + subexpr + subexpr + subexpr
_ite.setParseAction(lambda s, l, t: Ite(cond=t[0], t=t[1], e=t[2]))

subexpr <<= (basic
           | Suppress(LPAREN) + subexpr + Suppress(RPAREN)
           | add
           | subtract
           | minus
           | multiply
           | divide
           | leq
           | lt
           | geq
           | gt
           | eq
           | neq
           | _and
           | _or
           | _not
           | _let
           | _cond
           | _ite)

expr = subexpr | Group(LPAREN + subexpr + RPAREN)

vardecl = LPAREN + Ident + Ident + RPAREN


def make_vardecls_from_pairs(l):
    assert(len(l) % 2 == 0)
    vardecls = []
    i = 0
    while i < len(l) - 1:
        name = l[i]
        type = l[i + 1]
        vardecls.append((name, type))
        i += 2

    return vardecls

# only integer constants?
defconstant = LPAREN + Suppress("define-constant") + Ident + Integer + RPAREN
defconstant.setParseAction(lambda s, l, t: DefineConstant(name=t[0], val=t[1]))

defstatetype1 = LPAREN + Suppress("define-state-type") + Ident + (LPAREN + OneOrMore(vardecl) + RPAREN) + Group(LPAREN + OneOrMore(vardecl) + RPAREN) + RPAREN
defstatetype1.setParseAction(lambda s, l, t: DefineStateType(name=t[0], 
                                                             inputs=make_vardecls_from_pairs(t[1:-1]), 
                                                             vars=make_vardecls_from_pairs(t[-1])))
defstatetype2 = LPAREN + Suppress("define-state-type") + Ident + (LPAREN + OneOrMore(vardecl) + RPAREN) + RPAREN
defstatetype2.setParseAction(lambda s, l, t: DefineStateType(name=t[0],
                                                             inputs=[],
                                                             vars=make_vardecls_from_pairs(t[1:])))

defstatetype = defstatetype1 | defstatetype2

defstate = LPAREN + Suppress("define-states") + Ident + Ident + expr + RPAREN
defstate.setParseAction(lambda s, l, t: DefineStates(name=t[0], state_type=t[1], pred=unwrap(t[2])))

deftransition = LPAREN + Suppress("define-transition") + Ident + Ident + expr + RPAREN
deftransition.setParseAction(lambda s, l, t: DefineTransition(name=t[0], state_type=t[1], pred=unwrap(t[2])))

deftransitionsystem = LPAREN + Suppress("define-transition-system") + Ident + Ident + OneOrMore(expr) + RPAREN
deftransitionsystem.setParseAction(lambda s, l, t: DefineTransitionSystem(name=t[0], 
                                                                          state_type=t[1], 
                                                                          initial_states=unwrap(t[2]), 
                                                                          transition=unwrap(t[3])))

query = LPAREN + Suppress("query") + Ident + expr + RPAREN
query.setParseAction(lambda s, l, t: Query(name=t[0], query=unwrap(t[1])))

assume = LPAREN + Suppress("assume") + Ident + expr + RPAREN
assume.setParseAction(lambda s, l, t: Assume(system=t[0], assumption=unwrap(t[1])))

assumeinput = LPAREN + Suppress("assume-input") + Ident + expr + RPAREN
assumeinput.setParseAction(lambda s, l, t: Assume(system=t[0], assumption=unwrap(t[1])))

command = (query
           | defconstant
           | defstatetype
           | defstate
           | deftransition
           | deftransitionsystem
           | assume
           | assumeinput)

start = OneOrMore(command)

# ============= MAIN ================

def parseAllString(parser, string):
    res = parser.parseString(string, parseAll=True)
    return res

def strip_comments(file):
    text = ""
    for line in file:
        stripped = line.split(";;", 1)[0]
        text += stripped

    return text

def parse(file):
    string = strip_comments(file)
    return parseAllString(start, string)

def main():
    # tests()
    argparser = argparse.ArgumentParser(
                           prog='Sally parser',
                           description='Parses a Sally (.mcmt) file using pyparsing'
     )

    argparser.add_argument('filename')

    args = argparser.parse_args()
    file = open(args.filename)

    string = strip_comments(file)
    print(string)

    parsed = parse(string)


    for p in parsed:
        rich.print(p)



def tests():
    query_string1 = """(query T2 (and (<= x 20) (<= y 20)))"""
    query_string2 = """(query T2 (and (<= x 19) (<= y 19)))"""

    define_state_type_string1 = """
    (define-state-type my_state_type
        ((x Real) (y Real))
    )
    """


    define_state_type_string2 = """
    (define-state-type state_type_with_inputs
        ((x Real) (y Real))
        ((d Real))
    )
    """

    define_states_string1 = """
    (define-states x_is_zero my_state_type
        (= x 0)
    )
    """


    define_states_string2 = """
    (define-states initial_states my_state_type
        (and x_is_zero (= y 0))
    )
    """

    define_transition_string1 = """
    (define-transition inc_x_and_y my_state_type
        (and inc_x (= next.y (+ state.y 1)))
    )
    """


    define_transition_string2 = """
    (define-transition transition my_state_type
        (or
            (and (< state.x 20) inc_x_and_y)
            next.initial_states
        )
    )
    """

    define_transition_system_string1 = """
(define-transition-system T1 my_state_type
   (and (= x 0) (= y 0))
   (and (= next.x (+ state.x 1)) (= next.y (+ state.y 1)))
)
    """

    define_transition_system_string2 = """
(define-transition-system T2 my_state_type
   initial_states
   transition
)
    """


    define_transition_system_string3 = """
(define-transition-system T3 state_type_with_inputs
  (and (= x 0) (= y 0))
  (and (= next.x (+ state.x input.d))
   (= next.y (+ state.y input.d))
  )
)
    """

    assume_string1 = """
    (assume T3
        (and (<= x 100) (<= y 100))
    )
    """

    assumeinput_string1 = """
    (assume-input T3
        (>= d 0)
    )
    """

    if command.runTests([
        query_string1, query_string2, 
        define_state_type_string1, define_state_type_string2,
        define_states_string1, define_states_string2,
        define_transition_string1, define_transition_string2,
        define_transition_system_string1,
        define_transition_system_string2,
        define_transition_system_string3,
        assume_string1,
        assumeinput_string1
    ], print_results=False)[0]:
        print("ALL TESTS PASSED!")
    else:
        print("TESTS FAILED")



if __name__ == '__main__':
    main()