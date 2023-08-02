from dataclasses import dataclass
import argparse, rich

from typing import Tuple

from model import *
from model import Expression

import nuxmv_pyparser as Parser

"""
This file prototypes a translation from nuXmv to the IL 
using the parser located in nuxmv_pyparser.py 
(and its dependents module.py and utils.py).

TODO: consistent treatment of variable binding/scope

"""


res = []

@dataclass
class Expr:
    pass

@dataclass
class Access:
    module: Expr
    field: Expr


@dataclass
class ArrayType:
    domain: Expr
    range: Expr

@dataclass
class DeclareConst:
    constant: Expr
    sort: Expr

@dataclass
class ITE:
    cond: Expr
    t: Expr
    e: Expr

@dataclass
class Int:
    pass

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
    queries: list[Tuple[str, list[Expression]]]

counter = 0
def gensym(string):
    global counter
    counter += 1
    return string + str(counter)

def primed(string):
    return string + "'"


def ungensym(string):
    return ''.join([i for i in string if not i.isdigit()])


def translate_case_branches(branch_list, acc):
    if (branch_list == []):
        return acc
    else:
        head, *tail = branch_list
        cond, t = head
        acc = ITE(cond=cond, t=t, e=translate_case_branches(tail, None))
        return acc
    
def translate_expression(expr):
    ecn = expr.__class__.__name__
    if ecn == "Case":
        branch_list = list(vars(expr)['values'].items())
        return translate_case_branches(branch_list, None)
    # elif ecn == "Next":
    else: 
        return expr

def gather_outputs(results, name):
    for r in results:
        if (r.__class__.__name__ == "DefineSystem") and (r.name == name):
            locals = r.local
            vars = map(lambda x: x[0], locals)
            accessed_vars = map(lambda x: Access(r.name, x), vars)
            return list(accessed_vars)
        
    return []

def translate(parse_tree):
    results = []

    module_name = parse_tree['NAME']
    print("Translating", module_name)

    module_input = parse_tree['ARGS'].asList()

    module_local = []
    module_subsystems = []
    module_init = []
    module_trans = []
    module_inv = []
    module_output = []

    module_justice = []
    module_compassion = []
    module_query = []

    check = False

    for key, value in parse_tree.items():
        ugskey = ungensym(key)
     # ================== MINING VAR/IVAR =====================
        if ugskey == "VAR" or ugskey == "IVAR":
            add_to_locals = (ugskey == "VAR")
            add_to_inputs = (ugskey == "IVAR")
            for k, v in parse_tree[key].items():
                cn = v.__class__.__name__
                if cn == "Modtype":
                    data = vars(v)

                    subsys = Subsystem(synonym=k,
                                       name=data['modulename'],
                                       ivars=data['args'],
                                       ovars=gather_outputs(results, data['modulename']))
                    module_subsystems.append(subsys)
                elif cn == "Scalar":
                    enum_name = gensym("Enum")
                    des = DefEnumSort(name=enum_name, summands=vars(v)['values'].asList())
                    results.append(des)
                    if add_to_locals:
                        module_local.append((k, enum_name))
                    elif add_to_inputs:
                        module_input.append((k, enum_name))
                elif cn == "Range":
                    lo = vars(v)['start']
                    hi = vars(v)['stop']
                    module_inv.append(Ge(k, lo))
                    module_inv.append(Le(k, hi))
                    if add_to_locals:
                        module_local.append((k, "Int")) # make these classes?
                    elif add_to_inputs:
                        module_input.append((k, "Int"))
                elif cn == "Int":
                    if add_to_locals:
                        module_local.append((k, "Int"))
                    elif add_to_inputs:
                        module_input.append((k, "Int"))
                else:
                    if add_to_locals:
                        module_local.append((k, v))
                    elif add_to_inputs:
                        module_input.append((k, v))

        elif ugskey == "FROZENVAR":
            for k, v in parse_tree[key].items():
                primed_ident = Identifier(name=primed(str(k)))
                module_trans.append(Equal(left=primed_ident, right=k))
            pass
    # ================== MINING ASSIGN =====================
        elif ugskey == "ASSIGN":
            for k, v in parse_tree[key].items():
                kcn = k.__class__.__name__
                if kcn == "Smallinit":
                    module_init.append(Equal(left=vars(k)['value'], right=v))
                elif kcn == "Next":
                    case_translation = translate_expression(v)
                    primed_ident = Identifier(name=primed(str(vars(k)['value'])))
                    module_trans.append(Equal(left=primed_ident, right=case_translation))
                else:
                    module_inv.append(Equal(left=k, right=v))
    # ================== MINING DEFINE =====================
        elif ugskey == "DEFINE":
            for k, v in parse_tree[key].items():
                try:
                    module_init.append(Equal(left=vars(k)['name'], right=v))
                except KeyError:
                    module_init.append((Access(module=vars(k)['instance'], field=vars(k)['element']), v))
        elif ugskey == "CONSTANTS":
            # what do we do with non-typed symbolic constants?
            pass
        elif ugskey == "FUN":
            funs = parse_tree[key].asList()
            for fun in funs:
                name = fun.name
                typ = fun.type
                dom = typ.domain
                rng = typ.range

                results.append(DeclareConst(constant=name, sort=ArrayType(domain=dom, range=rng)))
            pass
        elif ugskey == "INIT":
            module_init += (parse_tree[key])
            pass
        elif ugskey == "INVAR":
            module_inv.append(parse_tree[key])
        elif ugskey == "TRANS":
            module_trans.append(parse_tree[key])
        elif ugskey == "FAIRNESS" or ugskey == "JUSTICE": # FAIRNESS is a backwards-compatible version of JUSTICE
            check = True
            module_justice.append(parse_tree[key])
        elif ugskey == "COMPASSION":
            check = True
            module_compassion.append(parse_tree[key])
        elif ugskey == "ISA": # deprecated feature to be removed
            mod_name = parse_tree[key]
            for res in results:
                match res:
                    case DefineSystem(name=n, input=mi, output=mo, local=ml, init=minit, trans=mt, inv=minv, subsystems=msub):
                        if mod_name == n:
                            module_input += mi
                            module_output += mo
                            module_local += ml
                            module_init += minit
                            module_trans += mt
                            module_inv += minv
                            module_subsystems += msub
                        else:
                            pass
                    case _:
                        pass
        elif ugskey == "PRED": # deal with `PRED <ident> := pr ;` case
            pr = parse_tree[key]
            module_init.append(pr)
        elif ugskey == "MIRROR":
            # what is this
            pass
                    

    for i in module_local:
        module_output.append(i)

    def_system = DefineSystem(name=module_name, 
                              input=module_input, 
                              output=module_output, 
                              local=module_local, 
                              init=module_init, 
                              trans=module_trans, 
                              inv=module_inv, 
                              subsystems=module_subsystems)
                              

    results.append(def_system)

    if check:
        check_system = CheckSystem(name=module_name,
                                   input=module_input,
                                   output=module_output,
                                   local=module_local,
                                   assumption=None,
                                   fairness=module_justice,
                                   reachable=None,
                                   queries=None)
    
        results.append(check_system)
    
    return results

def translate_list(parse_tree_list):
    global res
    i = 0
    main = 0
    for p in parse_tree_list:
        res += translate(p)
    res += translate(parse_tree_list[main])
    return res

def main():
    argparser = argparse.ArgumentParser(
                           prog='nuXmv/NuSMV parser',
                           description='Parses a nuXmv/NuSMV (.smv) file and translates the resulting AST into IL'
   )

    argparser.add_argument('filename')

    args = argparser.parse_args()

    file = open(args.filename)

    parse_tree = Parser.parse(file)
    for p in parse_tree:
        print(p)

    ast = translate_list(parse_tree)

    for a in ast:
        rich.print(a)
    

if __name__ == '__main__':
    main()
