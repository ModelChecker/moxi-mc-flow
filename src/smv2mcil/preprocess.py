import sys
import os
import re

file_path = sys.argv[1]

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

def module_names(file):
    names = []
    for line in file:
        spl = line.split(" ")
        if spl[0] == "MODULE":
            name = spl[1].split("(")[0]
            names.append(name.rstrip())

    return names

def handle_variables(file_path, module_names):
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
                    var_name = spl[0]
                    vspl = var_name.split(".")
                    if vspl[0] in module_names:
                        pass
                    else:
                        cleaned_var_name = var_name.replace('.', '_').replace(':', '')
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



try:
    with open(file_path, 'r') as file:
        names = module_names(file)
        new_file_contents = handle_variables(file_path, names)
        # print(new_file_contents)
        file.close()

    # print("NEW FILE CONTENTS:", new_file_contents)
    outfile_path = os.path.splitext(file_path)[0] + "-pp.smv"
    outfile = open(outfile_path, 'w+')
    outfile.write(new_file_contents)
    print(f"[preprocess.py] Wrote output to `{outfile_path}`")
    outfile.close()

except FileNotFoundError:
    print(f"File {file_path} not found!")