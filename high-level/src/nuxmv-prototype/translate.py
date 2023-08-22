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
class DeclareFun:
    name: str
    inputs: list[str]
    output: list[str]

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
class DeclareSort:
    name: str
    arity: int

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
    elif ecn == "Next":
        print("NEXT CASE!")
    else: 
        return expr


def conjoin_list(exp_list):
    if len(exp_list) == 0:
        return exp_list
    if len(exp_list) == 1:
        return exp_list[0]
    else:
        head, *tail = exp_list
        return And(head, conjoin_list(tail))

def typecheck_exp(exp):
    if str(exp) == "TRUE" or str(exp) == "FALSE":
        return Boolean()
    else:
        match exp.__class__.__name__:
            case "Lt" | "Gt":
                return Integer()
            case "And" | "Or" | "Iff" | "Not" | "Equal":
                return Boolean()
            case "Dot":
                global res
                for r in res:
                    match r:
                        case DefineSystem(name=name):
                            if str(name) == str(exp.instance):
                                print("FOUND DECLARATION OF MODULE", name)
                        case _:
                            print("FOUND", r)
            
        return f"UNIMPLEMENTED, {exp.__class__.__name__}"

module_components = {}
module_typecheck_status = {}

subsys_flag = False

# 1) loop through systems
#     - if we ever find a subsystem declaration, synthesize types for the parameters and assign them to
#       module parameters
#     - once we do so, mark the module inputs as being typechecked
# 2) for all declared variables in the submodules, synthesize their types
# 3) create variables representing said variables in the super module
def handle_modules(ast):
    # print("BEGIN: module components", module_components)
    for i, a in enumerate(ast):
        match a:
            case DefineSystem(name=name, input=input, output=_, local=local, init=init, trans=trans, inv=inv,
                              subsystems=subsysts):
                
                global subsys_flag
                if not subsys_flag:
                    break
            
                new_vars_types = []

                input_rebindings = []

                for (s, subsyst) in enumerate(subsysts):
                    subsyst_synonym = subsyst.synonym
                    subsyst_name = subsyst.name

                    input_exps = subsyst.ivars
                    output_exps = subsyst.ovars
                    input_typs = []
                    output_typs = []
                    
                    for ie in input_exps:
                        input_typs.append(typecheck_exp(ie))

                    for j, b in enumerate(ast):
                        match b:
                            case DefineSystem(name=name, input=input, output=output, 
                                              local=local, init=init, trans=trans, inv=inv, subsystems=subsys):
                                if (name == subsyst_name) and (not (name in module_typecheck_status)):
                                    new_input = list(zip(input, input_typs))
                                    old_output = module_components[subsyst_name][1]
                                    # print("MODULE COMPONENTS IN SUB LOOP", module_components[subsyst_name])
                                    module_components[subsyst_name] = (new_input, old_output)
                                    # print("NEW MODULE COMPONENTS IN SUB LOOP", module_components[subsyst_name])

                                    new_def_sys = DefineSystem(name=name,
                                                            input=new_input,
                                                            output=old_output,
                                                            local=local,
                                                            init=init,
                                                            trans=trans,
                                                            inv=inv,
                                                            subsystems=subsys)
                                    
                                    ast[j] = new_def_sys

                    # print("MIDDLE: module components", module_components)
                    new_inputs = []
                    new_outputs = []

                    for var in module_components[subsyst_name][0]:
                        new_inputs.append(var)
                    
                    for var in module_components[subsyst_name][1]:
                        new_outputs.append(var)

                    all_vars = new_inputs + new_outputs
                    # print("ALL VARS", all_vars)

                    all_updated_inputs = []
                    all_updated_outputs = []
                    for (comp, typ) in all_vars:
                        new_name = str(subsyst_synonym) + "_" + str(comp)
                        new_vars_types.append((new_name, typ))
                        new_input_names = list(map(lambda x : x[0], new_inputs))
                        new_output_names = list(map(lambda x : x[0], new_outputs))
                        if comp in new_input_names:
                            all_updated_inputs.append((Identifier(name=new_name), typ))
                        elif comp in new_output_names:
                            all_updated_outputs.append((Identifier(name=new_name), typ))


                    all_updated_inputs_no_types = list(map(lambda x : x[0], all_updated_inputs))
                    all_updated_outputs_no_types = list(map(lambda x : Identifier(name=x[0]), all_updated_outputs))
                    new_subsyst = Subsystem(synonym=subsyst_synonym,
                                            name=subsyst_name,
                                            ivars=all_updated_inputs_no_types,
                                            ovars=all_updated_outputs_no_types)
                    
                    input_rebindings += list(zip(all_updated_inputs, input_exps))
                    
                    subsysts[s] = new_subsyst
                        
                    module_typecheck_status[subsyst_name] = True
                        
                new_output = new_vars_types


                new_invs_list = []
                for (l, r) in input_rebindings:
                    new_invs_list.append(Equal(l[0], r))
                new_invs = conjoin_list(new_invs_list)

                new_def_sys2 = DefineSystem(name=name, 
                                                 input=input, 
                                                 output=new_output,
                                                 local=local, 
                                                 init=init, 
                                                 trans=trans, 
                                                 inv=new_invs,
                                                 subsystems=subsysts)
                
                
                ast[i] = new_def_sys2
                    

    return ast


def translate(parse_tree):
    results = []

    module_name = parse_tree['NAME']


    module_input = parse_tree['ARGS'].asList()
    module_components[module_name] = ([], [])
    for a in module_input:
        module_components[module_name][0].append(a)

    

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
     # ================== MINING VAR/IVAR/FROZENVAR =====================
        if ugskey == "VAR" or ugskey == "IVAR":
            add_to_output = (ugskey == "VAR")
            add_to_inputs = (ugskey == "IVAR")
            for k, v in parse_tree[key].items():
                if add_to_output:
                    module_components[module_name][1].append((k, v))
                elif add_to_inputs:
                    module_components[module_name][0].append((k, v))
                cn = v.__class__.__name__
                if cn == "Modtype":
                    data = vars(v)

                    global subsys_flag
                    subsys_flag = True

                    subsys = Subsystem(synonym=k,
                                       name=data['modulename'],
                                       ivars=data['args'],
                                       ovars=module_components[data['modulename']][1])

                    module_subsystems.append(subsys)
                elif cn == "Scalar":
                    enum_name = gensym("Enum")
                    des = DefEnumSort(name=enum_name, summands=vars(v)['values'].asList())
                    results.append(des)
                    if add_to_output:
                        module_output.append((k, enum_name))
                    elif add_to_inputs:
                        module_input.append((k, enum_name))
                elif cn == "Range":
                    lo = vars(v)['start']
                    hi = vars(v)['stop']
                    module_inv.append(Ge(k, lo))
                    module_inv.append(Le(k, hi))

                    if add_to_output:
                        module_output.append((k, "Int")) # make these classes?
                    elif add_to_inputs:
                        module_input.append((k, "Int"))
                elif cn == "Int":
                    if add_to_output:
                        module_output.append((k, "Int"))
                    elif add_to_inputs:
                        module_input.append((k, "Int"))
                else:
                    if add_to_output:
                        module_output.append((k, v))
                    elif add_to_inputs:
                        module_input.append((k, v))

        elif ugskey == "FROZENVAR":
            frozen_invs = []
            for k, v in parse_tree[key].items():
                primed_ident = Identifier(name=primed(str(k)))
                module_output.append((k, v))
                frozen_invs.append(Equal(left=primed_ident, right=k))
            module_inv.append(conjoin_list(frozen_invs))
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
                tcev = typecheck_exp(v)

                module_components[module_name][1].append((k, tcev))

                module_output.append((k, tcev))
                try:
                    module_inv.append(Equal(left=vars(k)['name'], right=v))
                except KeyError:
                    module_inv.append((Access(module=vars(k)['instance'], field=vars(k)['element']), v))
        elif ugskey == "CONSTANTS":
            results.append(DeclareSort("Const", 0))
            for c in parse_tree[key]:
                results.append(DeclareConst(constant=c, sort="Const"))
        elif ugskey == "FUN":
            funs = parse_tree[key].asList()
            for fun in funs:
                name = fun.name
                typ = fun.type

                dom = typ.domain
                rng = typ.range
                # results.append(DeclareFun(name=name, inputs=dom, output=rng))
                results.append(DeclareConst(constant=name, sort=ArrayType(domain=dom, range=rng)))
            pass
        elif ugskey == "INIT":
            module_init += (parse_tree[key])
            pass
        elif ugskey == "INVAR":
            module_inv += (parse_tree[key])
        elif ugskey == "TRANS":
            module_trans += (parse_tree[key])
        elif ugskey == "FAIRNESS" or ugskey == "JUSTICE": # FAIRNESS is a backwards-compatible version of JUSTICE
            check = True
            module_justice.append(parse_tree[key])
        elif ugskey == "COMPASSION":
            check = True
            module_compassion.append(parse_tree[key])
        elif ugskey == "ISA" or ugskey == "PRED" or ugskey == "MIRROR": # deprecated feature to be removed
            assert(False)
        elif ugskey == "INVARSPEC":
            check = True
            module_query.append(parse_tree[key])
                    

    for i in module_local:
        module_output.append(i)

    def_system = DefineSystem(name=module_name, 
                              input=module_input, 
                              output=module_output, 
                              local=module_local, 
                              init=conjoin_list(module_init), 
                              trans=conjoin_list(module_trans), 
                              inv=conjoin_list(module_inv), 
                              subsystems=module_subsystems)
                              

    results.append(def_system)

    if check:
        check_system = CheckSystem(name=module_name,
                                   input=module_input,
                                   output=module_output,
                                   current=[],
                                   local=module_local,
                                   assumption=None,
                                   fairness=module_justice,
                                   reachable=None,
                                   queries=module_query)
    
        results.append(check_system)
    return results

def translate_list(parse_tree_list):
    global res
    main_idx = 0
    i = 0
    for p in parse_tree_list:

        if str(p['NAME']) == "main":
            main_idx = i
        else: 
            res += translate(p)
        i += 1

    res += translate(parse_tree_list[main_idx])
    return res

def translate_parse_tree(parse_tree, print_ast=False):
    ast = translate_list(parse_tree)
    hmast = handle_modules(ast)

    global res
    res = hmast

    if print_ast:
        rich.print(hmast)

    return hmast

def main():
    argparser = argparse.ArgumentParser(
                           prog='nuXmv/NuSMV parser',
                           description='Parses a nuXmv/NuSMV (.smv) file and translates the resulting AST into IL'
   )

    argparser.add_argument('filename')

    args = argparser.parse_args()

    file = open(args.filename)

    parse_tree = Parser.parse(file)

    rich.print(translate_parse_tree(parse_tree))


if __name__ == '__main__':
    main()
