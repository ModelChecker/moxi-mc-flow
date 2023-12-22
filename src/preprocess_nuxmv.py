from io import TextIOWrapper
import sys
import os
import argparse
from pathlib import Path


var_kws = ["IVAR", "VAR", "FROZENVAR"]

section_kws = ["VAR", 
               "IVAR", 
               "FROZENVAR", 
               "FUN", 
               "DEFINE", 
               "CONSTANTS", 
               "ASSIGN", 
               "TRANS", 
               "INIT", 
               "INVAR",
               "FAIRNESS",
               "JUSTICE",
               "COMPASSION",
               "MODULE",
               "PRED",
               "MIRROR",
               "ISA",
               "CTLSPEC",
               "SPEC",
               "LTLSPEC",
               "INVARSPEC",
               "COMPUTE",
               "PSLSPEC"]

def module_names(file: TextIOWrapper) -> list[str]:
    names: list[str] = []
    for line in file:
        spl = line.split(" ")
        if spl[0] == "MODULE":
            name = spl[1].split("(")[0]
            names.append(name.rstrip())

    return names

def handle_variables(file_path: str, module_names: list[str]):
    with open(file_path, 'r') as file:
        with open(file_path, 'r') as file2:
            var_decl = False

            file_contents = file2.read()

            ret_fc = file_contents
            for line in file:
                if line.rstrip() in section_kws:
                    var_decl = False
                if line.rstrip() in var_kws: # at variable declaration site!
                    var_decl = True
                    continue
                
                if var_decl:
                    spl = line.rstrip().split(": ")
                    var_name = spl[0].rstrip()
                    vspl = var_name.split(".")
                    if vspl[0] in module_names:
                        pass
                    else:
                        cleaned_var_name = var_name.replace('.', '_').replace(':', '').replace("\"","").replace('$', '')
                        if cleaned_var_name == var_name:
                            continue
                        else:
                            # print(f"replacing {var_name} with {cleaned_var_name}")
                            # if ret_fc.find(var_name) != -1:
                            #     print(f"FOUND {var_name}")
                            new_ret_fc = ret_fc.replace(var_name, cleaned_var_name)
                            # if ret_fc == new_ret_fc:
                            #     print("NO CHANGE")
                            ret_fc = new_ret_fc

            return ret_fc


def preprocess(input: Path) -> str:
    with open(str(input), 'r') as file:
        names = module_names(file)
        return handle_variables(str(input), names)


# if __name__ == "__main__":
#     argparser = argparse.ArgumentParser(
#                             prog='preprocess script for nuXmv files',
#     )
#     argparser.add_argument("input")
#     argparser.add_argument("output")

#     args = argparser.parse_args()

#     input_path = Path(args.input)
#     output_path = Path(args.output)

#     new_file_contents = preprocess(input_path)

#     with open(str(output_path), 'w') as file:
#         file.write(new_file_contents)

#     print(f"[preprocess.py] Wrote output to `{output_path}`")
