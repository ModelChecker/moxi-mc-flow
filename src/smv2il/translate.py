from dataclasses import dataclass
import argparse, rich

from typing import Tuple

if __package__ == "":
    from model import *
else:
    from .model import *

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


def conjoin_list(exp_list):
    if len(exp_list) == 0:
        return exp_list
    if len(exp_list) == 1:
        return exp_list[0]
    else:
        head, *tail = exp_list
        return And(head, conjoin_list(tail))
    
def disjoin_list(exp_list):
    if len(exp_list) == 0:
        return exp_list
    if len(exp_list) == 1:
        return exp_list[0]
    else:
        head, *tail = exp_list
        return Or(head, disjoin_list(tail))


def translate_case_branches(branch_list, acc, lhs):
    if (branch_list == []):
        return acc
    else:
        head, *tail = branch_list
        cond, t = head

        if (t.__class__.__name__ == "Set"):
            # print("Set", lhs)
            disjuncts = []
            for elem in t.elements:
                disjuncts.append(Equal(left=Identifier(primed(lhs.name)), right=elem))
            t = disjoin_list(disjuncts)
            acc = ITE(cond=cond, t=t, e=translate_case_branches(tail, None, lhs))
            return acc

        acc = ITE(cond=cond, t=Equal(left=Identifier(primed(lhs.name)), right=t), e=translate_case_branches(tail, None, lhs))
        return acc
    
def translate_expression(expr, lhs=None):
    ecn = expr.__class__.__name__
    if ecn == "Case":
        branch_list = list(vars(expr)['values'].items())
        return translate_case_branches(branch_list, [], lhs)
    elif ecn == "Next":
        return Identifier(name=primed(expr.value.name))
    elif ecn == "Not":
        return Not(translate_expression(expr.value, lhs))
    elif ecn == "Identifier":
        return Identifier(expr)
    elif ecn == "And":
        return And(left=translate_expression(expr.left, lhs),
                  right=translate_expression(expr.right, lhs))
    elif ecn == "Or":
        return Or(left=translate_expression(expr.left, lhs),
                  right=translate_expression(expr.right, lhs))
    elif ecn == "Equal":
        return Equal(left=translate_expression(expr.left, lhs),
                     right=translate_expression(expr.right, lhs))
    elif ecn == "Implies":
        return Implies(left=translate_expression(expr.left, lhs),
                       right=translate_expression(expr.right, lhs))
    elif ecn == "Iff":
        return Iff(left=translate_expression(expr.left, lhs),
                   right=translate_expression(expr.right, lhs))
    elif ecn == "list":
        return list(map(lambda x : translate_expression(x, lhs), expr))
    elif ecn == "int":
        return expr
    elif ecn == "Add":
        return Add(left=translate_expression(expr.left, lhs),
                  right=translate_expression(expr.right, lhs))
    elif ecn == "Sub":
        return Sub(left=translate_expression(expr.left, lhs),
                   right=translate_expression(expr.right, lhs))
    elif ecn == "Dot":
        return Dot(instance=expr.instance, element=expr.element)
    elif ecn == "Conversion":
        # print("CONVERSION")
        return translate_expression(expr.value)
    elif ecn == "NumberWord":
        return expr
    elif ecn == "Concat":
        return Concat(left=translate_expression(expr.left, lhs),
                      right=translate_expression(expr.right, lhs))
    elif ecn == "BitSelection":
        return BitSelection(word=translate_expression(expr.word, lhs),
                            start=expr.start,
                            stop=expr.stop)
    elif ecn == "Lt":
        return Lt(left=translate_expression(expr.left, lhs),
                  right=translate_expression(expr.right, lhs))
    elif ecn == "Xor":
        return Xor(left=translate_expression(expr.left, lhs),
                   right=translate_expression(expr.right, lhs))
    else: 
        print("else case", expr, ecn)
        return expr


def WordConstantType(wconstant):
    assert(wconstant[0] == "0")
    idx = 1
    if (wconstant[idx] == "u") or (wconstant[idx] == "s"):
        idx += 1

    if (wconstant[idx] == "b") or (wconstant[idx] == "B") \
    or (wconstant[idx] == "d") or (wconstant[idx] == "D") \
    or (wconstant[idx] == "h") or (wconstant[idx] == "H"):
        idx += 1

    end_idx = idx

    while(wconstant[end_idx] != "_"):
        end_idx += 1

    return int(wconstant[idx:end_idx])



def typecheck_exp(exp, context=None):
    print("TYPECHECKING", exp)
    if str(exp) == "TRUE" or str(exp) == "FALSE":
        return Boolean()
    else:
        match exp.__class__.__name__:
            case "Minus":
                tl = typecheck_exp(exp.value, context)
                return tl
            case "Add" | "Sub" | "Div" | "Mult" | "Mod":
                tl = typecheck_exp(exp.left, context)
                return tl
            case "Not":
                tl = typecheck_exp(exp.value, context)
                if tl.__class__.__name__ == "Boolean":
                    return Boolean()
                else:
                    assert(False)
                    return MWord(tl.size)
            case "Equal" | "NotEqual":
                return Boolean()
            case "Lt" | "Gt" | "Le" | "Ge":
                return Boolean()
            case "And" | "Or" | "Iff" | "Xor" | "Xnor":
                tl = typecheck_exp(exp.left, context)
                if tl.__class__.__name__ == "Boolean":
                    return Boolean()
                elif tl.__class__.__name__ == "Dot":
                    return typecheck_exp(exp.right, context) # HACK: FIX THIS LATER
                else:
                    # assert(tl.__class__.__name__ == 'MWord')
                    # raise KeyError(tl, tl.__class__.__name__)
                    # print("Expr", exp)
                    return MWord(tl.size)
            case "RShift":
                tl = typecheck_exp(exp.left, context)
                return tl
            case "Dot": # handle this after handling modules
                return Dot(instance=exp.instance, element=exp.element)
            # case "ITE":
            #     print("ITE", exp)
            #     tb = exp.t
            #     return typecheck_exp(tb, context)
            case "Case":
                # print("CASE", exp.values)
                v0 = None
                for c, v in exp.values.items():
                    v0 = v
                    break
                # print("typechecking branch value", v0)
                return typecheck_exp(v0, context)
            case "Concat":
                bv1 = typecheck_exp(exp.left, context)
                # print("bv1 type", bv1)
                bv2 = typecheck_exp(exp.right, context)
                # print("bv2 type", bv2)
                return MWord(size=bv1.size + bv2.size)
            case "BitSelection":
                lo = exp.start
                hi = exp.stop
                # if (hi - lo + 1 < 0):
                #     print("EXPR", exp)
                #     raise KeyError()
                return MWord(size=abs(hi - lo) + 1)
            case "Conversion":
                if (exp.target_type == "unsigned") or (exp.target_type == "signed"):
                    v = typecheck_exp(exp.value, context)
                    return v
                else:
                    return f"Unimplemented, {exp.target_type}"
                # print("CONVERSION")
            case "NumberWord":
                return MWord(size=WordConstantType(exp.value))
            case "Next":
                return typecheck_exp(exp.value, context)
            case "Identifier":
                # print(context)
                for (c, t) in context:
                    if exp == c:
                        return t
    return (f"UNIMPLEMENTED, {exp.__class__.__name__}")

module_components = {}
module_typecheck_status = {}

subsys_flag = False

def resolve_vars(vars):
    for i, (e, t) in enumerate(vars):
        match t:
            case Dot(instance=mod, element=elem):
                # print("DOT CASE")
                instance = mod
                element = elem
                var_name = mod.name + "_" + elem.name
                # print(instance, "DOT", element)
                global res
                for r in res:
                    rcn = r.__class__.__name__
                    if rcn == "DefineSystem":
                            # print("DEFINE SYSTEM CASE")
                            # print("looking at", r.name, "in search of", var_name)
                            if r.output == None:
                                continue
                            else:
                                for (s, newty) in r.output:
                                    # print(f"RESOLVING {newty} in {r.output}")
                                    if str(var_name) == str(s):
                                        vars[i] = (e, newty)
            case _:
                vars[i] = (e, t)

    return vars

def resolve_refs(ast):
    for i, a in enumerate(ast):
        match a:
            case DefineSystem(name=name, input=input, output=output, local=local, init=init, trans=trans, inv=inv, subsystems=subsysts):
                ds = DefineSystem(name=name,
                                    input=resolve_vars(input),
                                    output=resolve_vars(output),
                                    local=resolve_vars(local),
                                    init=init,
                                    trans=trans,
                                    inv=inv,
                                    subsystems=subsysts)
                ast[i] = ds
            case _:
                ast[i] = a
    return ast

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
            case DefineSystem(name=name, input=input, output=output, local=local, init=init, trans=trans, inv=inv,
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
                        context = output
                        # print("HANDLE MODULES TYPECHECKING ", ie)                        
                        input_typs.append(typecheck_exp(ie, context))
                    # print("HANDLE MODULES", input_typs)

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
                    if (v.__class__.__name__ == "Case"):
                        case_translation = translate_expression(v, k.value)
                        module_trans.append(case_translation)
                    else:
                        primed_ident = Identifier(name=primed(str(vars(k)['value'])))
                        module_trans.append(Equal(left=primed_ident, right=translate_expression(v, k.value)))
                else:
                    module_inv.append(Equal(left=k, right=v))
    # ================== MINING DEFINE =====================
        elif ugskey == "DEFINE":
            for k, v in parse_tree[key].items():
                # v = translate_expression(v, lhs=k)
                tcev = typecheck_exp(v, module_output)

                module_components[module_name][1].append((k, tcev))

                module_output.append((k, tcev))
                try:
                    module_inv.append(Equal(left=vars(k)['name'], right=translate_expression(v, lhs=k)))
                except KeyError:
                    module_inv.append((Access(module=vars(k)['instance'], field=vars(k)['element']), translate_expression(v, lhs=k)))
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
            module_init += (translate_expression(parse_tree[key]))
            pass
        elif ugskey == "INVAR":
            module_inv += (translate_expression(parse_tree[key]))
        elif ugskey == "TRANS":
            module_trans += (translate_expression(parse_tree[key], None))
        elif ugskey == "FAIRNESS" or ugskey == "JUSTICE": # FAIRNESS is a backwards-compatible version of JUSTICE
            check = True
            module_justice.append(translate_expression(parse_tree[key]))
        elif ugskey == "COMPASSION":
            check = True
            module_compassion.append(translate_expression(parse_tree[key]))
        elif ugskey == "ISA" or ugskey == "PRED" or ugskey == "MIRROR": # deprecated feature to be removed
            assert(False)
        elif (ugskey == "SPEC" or ugskey == "CTLSPEC"):
            raise ValueError("CTL specifications are not supported!")
        elif ugskey == "INVARSPEC":
            check = True
            module_query.append(translate_expression(parse_tree[key]))
                    

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

    res_ast = resolve_refs(hmast)

    res = res_ast

    if print_ast:
        rich.print(res_ast)

    return res_ast

def main():
    argparser = argparse.ArgumentParser(
                           prog='nuXmv/NuSMV parser',
                           description='Parses a nuXmv/NuSMV (.smv) file and translates the resulting AST into IL'
   )

    argparser.add_argument('filename')

    args = argparser.parse_args()

    file = open(args.filename)

    import nuxmv_pyparser as Parser
    parse_tree = Parser.parse(file)

    rich.print(translate_parse_tree(parse_tree))


if __name__ == '__main__':
    main()
