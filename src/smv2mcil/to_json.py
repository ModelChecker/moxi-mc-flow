import argparse, rich
import json

if __package__ == "":
    from translate import *
else:
    from .translate import *



# FORMAT:
# 1) 0
# 2) optional u/s
# 3) b/B, o/O, d/D, h/H
# 4) optional # of bits
# 5) _
# 6) constant value

# for the moment, only deal with decimal values
def word_constant_json(wconstant):
    assert(wconstant.__class__.__name__ == "NumberWord")

    wc = wconstant.value

    print("WCONSTANT", wconstant)

    fmt = max(wc.find("d"), wc.find("D"))
    if fmt == -1:
            raise ValueError("non-decimal word constants not supported")

    
    uscore = wc.find("_")

        
    if uscore == -1:
        raise ValueError("word constants need underscores")
        
    const = wc[uscore + 1:]

    bin_const = bin(int(const))[2:] # removes 0b from start
    print("word:", wc, "const:", const, "bin_const:", bin_const)

    return {
        "identifier": ("#b" + bin_const)
    }

def expr_json(expr):
    ecn = expr.__class__.__name__
    if ecn == "NoneType":
        raise ValueError("ecn can't be NoneType")
    match ecn:
        case "list":
            return {
                "identifier": "True"
            }
        case "And":
            return {
                "identifier": "and",
                "args": [
                    expr_json(expr.left),
                    expr_json(expr.right)
                ]
            }
        case "Or":
            return {
                "identifier": "or",
                "args": [
                    expr_json(expr.left),
                    expr_json(expr.right)
                ]
            }
        case "Not":
            return {
                "identifier": "not",
                "args": [
                    expr_json(expr.value)
                ]
            }
        case "Equal":
            return {
                "identifier": "=",
                "args": [
                    expr_json(expr.left),
                    expr_json(expr.right)
                ]
            }

        case "Xor":
            return {
                "identifier": "xor",
                "args": [
                    expr_json(expr.left),
                    expr_json(expr.right)
                ]
            }
        case "Identifier":
            e = expr

            # todo: fix nests of identifiers
            while e.__class__.__name__ != "str":
                e = e.name

            ret = ""
            if e == "TRUE":
                ret = "True"
            elif e == "FALSE":
                ret = "False"
            else:
                ret = e
            return {
                "identifier": ret
            }
        case "Dot":
            return {
                "identifier": expr.instance.name + "_" + expr.element.name
            }
        case "ITE":
            if expr.e == None:
                return {
                    "identifier": "ite",
                    "args": [
                        expr_json(expr.cond),
                        expr_json(expr.t)
                    ]
                }
            else:
                return {
                    "identifier": "ite",
                    "args": [
                        expr_json(expr.cond),
                        expr_json(expr.t),
                        expr_json(expr.e)
                    ]
                }
        case "Set":
            return {
                "identifier": "set",
                "args": list(map(lambda x : { "identifier": x.name }, expr.elements))
            }
        case "Implies":
            return {
                "identifier": "implies",
                "args": [
                    expr_json(expr.left),
                    expr_json(expr.right)
                ]
            }
        case "Iff":
            return {
                "identifier": "iff",
                "args": [
                    expr_json(expr.left),
                    expr_json(expr.right)
                ]
            }
        case "int":
            return {
                "identifier": expr
            }
        case "str":
            return {
                "identifier": expr
            }
        case "Add":
            return {
                "identifier": "+",
                "args": [
                    expr_json(expr.left),
                    expr_json(expr.right)
                ]
            }
        case "Sub":
            return {
                "identifier": "-",
                "args": [
                    expr_json(expr.left),
                    expr_json(expr.right)
                ]
            }
        case "Lt":
            return {
                "identifier": "<",
                "args": [
                    expr_json(expr.left),
                    expr_json(expr.right)
                ]
            }
        case "RShift":
            return {
                "identifier": ">>",
                "args": [
                    expr_json(expr.left),
                    expr_json(expr.right)
                ]
            }
        case "Concat":
            return {
                "identifier": "concat",
                "args": [
                    expr_json(expr.left),
                    expr_json(expr.right)
                ]
            }
        case "BitSelection":
            return {
                "identifier": "extract",
                "args": [
                    expr_json(expr.start),
                    expr_json(expr.stop),
                    expr_json(expr.word)
                ]
            }
        case "Conversion":
            return expr_json(expr.value)
        case "NumberWord":
            return word_constant_json(expr)
        case _:
            raise ValueError("match all exprs", ecn, expr)

def subsystem_json(subsystem):
    synonym = subsystem.synonym
    name = subsystem.name
    ivars = subsystem.ivars
    ovars = subsystem.ovars
    vars = ivars + ovars

    nvars = []
    for v in vars:
        while v.__class__.__name__ != "str":
            v = v.name
        nvars.append(v)

    return {
        "symbol": synonym.name,
        "target": {
            "symbol": name.name,
            "arguments": nvars
        }
    }

def type_to_sort(typ):
    tcn = typ.__class__.__name__
    match tcn:
        case "Boolean":
            return {
                "identifier": "Bool"
            }
        case "Integer":
            return {
                "identifier": "Int"
            }
        case "MWord":
            return {
                "identifier": {
                    "symbol": "BitVec",
                    "indices": [typ.size]
                }
            }
        case "ArrayType": # fix this
            return {
                "symbol": "Array",
                "domain": type_to_sort(typ.domain),
                "range": type_to_sort(typ.range)
            }
        case "Prod": # fix this
            return {
                "symbol": "Prod",
                "args": list(map(lambda x : type_to_sort(x), typ.list))
            }
        case "str": # enum
            return {
                "identifier": typ
            }
        case _:
            raise ValueError("match all types", tcn, typ)


def var_json(var_list):
    result = []
    for (var, typ) in var_list:
        if var.__class__.__name__ == "str":
            result.append({
                "symbol": var,
                "sort": type_to_sort(typ)
            })
        else:
            result.append({
                "symbol": var.name,
                "sort": type_to_sort(typ)
            })


    return result

def to_json(ast):
    result = []
    for a in ast:
        match a:
            case DefineSystem(name=name, 
                              input=input,
                              output=output,
                              local=local,
                              init=init,
                              trans=trans,
                              inv=inv,
                              subsystems=subsys):

                j = {
                    "command": "define-system",
                    "symbol": name.name,
                    "input": var_json(input),
                    "output": var_json(output),
                    "local": local,
                    "init": expr_json(init),
                    "trans": expr_json(trans),
                    "inv": expr_json(inv),
                    "subsys": list(map(lambda x : subsystem_json(x), subsys))
                }
                result.append(j)
            case CheckSystem(name=name,
                             input=input,
                             output=output,
                             local=local,
                             assumption=assumption,
                             fairness=fairness,
                             current=current,
                             reachable=reachable,
                             queries=queries):
                
                name_str = name
                if name.__class__.__name__ == 'Identifier':
                    name_str = name.name


                
                j = {
                    "command": "check-system",
                    "symbol": name_str,
                    "input": var_json(input),
                    "output": var_json(output),
                    "local": local,
                    "assumption": assumption,
                    "fairness": fairness,
                    "reachable": reachable,
                    "current": current,
                    "queries": 
                    list(map(lambda x : \
                             list(map(lambda x : expr_json(x), x)), queries))
                }

                if assumption == None:
                    j['assumption'] = []
                
                if reachable == None:
                    j['reachable'] = []

                result.append(j)

            case DeclareConst(constant=const, sort=sort):
                j = {
                    "command": "declare-const",
                    "symbol": const.name,
                    "sort": type_to_sort(sort)
                }
                result.append(j)

            case DefEnumSort(name=name, summands=summands):
                j = {
                    "command": "declare-enum-sort",
                    "symbol": name,
                    "values": list(map(lambda x : x.name, summands))
                }
                result.append(j)
            case _:
                raise ValueError("match all il commands", a)

    return result


def ast_to_json_to_file(ast, filename, print_json=False):
    json_list = to_json(ast)

    if print_json:
        rich.print(json_list)

    with open(filename, "w+") as json_file:
        json.dump(json_list, json_file, ensure_ascii=False)



def main():
    argparser = argparse.ArgumentParser(
                           prog='IL AST to JSON',
                           description='Converts an IL AST (described in translate.py) into a JSON object (conforming to the IL schema)'
   )

    argparser.add_argument('filename')

    args = argparser.parse_args()

    file = open(args.filename)

    parse_tree = Parser.parse(file)
    ast = translate_parse_tree(parse_tree, print_ast=False)

    json_list = to_json(ast)
    rich.print(json_list)

    main_filename = args.filename.split("/")[-1]
    file_prefix = main_filename.split(".")[0]
    new_filename = file_prefix + ".json"
    print(new_filename)
    with open(new_filename, "w+") as json_file:
        json.dump(json_list, json_file, ensure_ascii=False, indent=4)


if __name__ == '__main__':
    main()