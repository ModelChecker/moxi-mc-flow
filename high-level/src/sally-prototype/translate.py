from dataclasses import dataclass
import argparse, rich
from typing import Tuple

from sally_pyparser import Expression, DefineConstant, \
    DefineStateType, DefineStates, DefineTransition, DefineTransitionSystem, \
    Assume, Query


"""
This file prototypes a translation from Sally to the IL
using the parser located in sally_pyparser.py

TODO: finish implementation (propagate gathered aliases, debugging)

"""


import sally_pyparser as Parser

# maps `my_state_type` |~~> variables defined in `define-state-type`
state_var_dict = dict()

# think of `define-states` as an alias definition mechanism
# `(define-states name type expr)` creates an alias for `expr` called `name`
# we don't really care about the type since we assume all input specs are typechecked
state_def_dict = dict()

# similar to the def_dict above (creating aliases for two-state transitions)
state_trans_dict = dict()

# tracks all `DefineSystem` calls up to this point
system_dict = dict()

assumption_dict = dict()

query_dict = dict()


counter = 0
def gensym(string):
    global counter
    counter += 1
    return string + str(counter)

@dataclass
class DeclareConstant:
    name: str
    val: str

@dataclass
class Subsystem:
    synonym: str
    name: str
    ivars: list[str]
    ovars: list[str]

@dataclass
class DefineSystem:
    name: str
    input: list[str]
    output: list[str]
    local: list[Tuple[str, Expression]]
    init: Expression
    trans: Tuple[Expression, Expression]
    inv: Expression
    subsystems: list[Subsystem]

@dataclass
class DefEnumSort:
    name: str
    summands: list[str]

@dataclass
class CheckSystem:
    name: str
    input: list[Tuple[str, Expression]]
    output: list[Tuple[str, Expression]]
    local: list[Tuple[str, Expression]]
    assumption: Tuple[str, Expression]
    fairness: Tuple[str, Expression]
    reachable: Tuple[str, Expression]
    current: Tuple[str, Expression]
    query: Tuple[str, list[Expression]]
    queries: list[Tuple[str, list[Expression]]]


def primed(string):
    return string + "'"

def var_replace(string):
    if string[0:4] == 'next':
        return primed(string[5:])
    if string[0:5] == 'state':
        return string[6:]
    
    return string

def translate(parse_tree):
    res = []
    for p in parse_tree:
        match p:
            case DefineConstant(name, val):
                res.append(DeclareConstant(name, val))
            case DefineStateType(name, inputs, vars):
                state_var_dict[name] = (inputs, vars) # to be used in DefineSystem/DefineTransitionSystem
            case DefineStates(name, state_type, pred):
                state_def_dict[name] = pred
            case DefineTransition(name, state_type, pred):
                state_trans_dict[name] = pred
            case DefineTransitionSystem(name, state_type, initial_states, transition):
                (inputs, locals) = state_var_dict[state_type]
                query_dict[name] = []
                assumption_dict[name] = []
                
                try:
                    initial = state_def_dict[state_type]
                except KeyError:
                    initial = initial_states

                try:
                    trans = state_trans_dict[state_type]
                except KeyError:
                    trans = transition

                ds = DefineSystem(name=name,
                                  input=inputs,
                                  output=locals,
                                  local=locals,
                                  init=initial,
                                  trans=trans,
                                  inv=[],
                                  subsystems=[])

                system_dict[name] = ds

                res.append(ds) 
            case Assume(system, assumption):
                try:
                    assumption_dict[system].append(assumption)
                except KeyError:
                    pass
            case Query(name, query):
                try:
                    query_dict[name].append((name + gensym("query"), query))
                except KeyError:
                    pass
            # case Interpolate:
            #     pass
            # case Generalize:
            #     pass
            # case Checksat:
            #     pass

    for (name, query) in query_dict.items():
        ds = system_dict[name]
        cs = CheckSystem(name=name,
                         input=ds.input,
                         output=ds.output,
                         local=ds.local,
                         assumption=assumption_dict[name],
                         fairness=[],
                         reachable=[],
                         current=[],
                         query=[],
                         queries=query
                         )
        res.append(cs)

    return res



def main():
    argparser = argparse.ArgumentParser(
                           prog='Sally translator',
                           description='Parses a Sally (.mcmt) file and translates it into the IL.'
   )

    argparser.add_argument('filename')

    args = argparser.parse_args()

    file = open(args.filename)

    parse_tree = Parser.parse(file)

    ast = translate(parse_tree)

    # print("STATE VAR DICT", state_var_dict)
    # print("STATE DEF DICT", state_def_dict)
    # print("STATE TRANS DICT", state_trans_dict)
    # print("SYSTEM DICT", system_dict)
    # print("ASSUMPTION DICT", assumption_dict)
    # print("QUERY DICT", query_dict)

    for a in ast:
        rich.print(a)

if __name__ == '__main__':
    main()



