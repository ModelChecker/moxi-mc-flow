from pathlib import Path
import subprocess

from .util import logger

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

def get_module_names(content: str) -> list[str]:
    names: list[str] = []
    for line in content.splitlines():
        spl = line.split(" ")
        if spl[0] == "MODULE":
            name = spl[1].split("(")[0]
            names.append(name.rstrip())

    return names

def handle_variables(content: str, module_names: list[str]):
    var_decl = False

    ret_fc = content
    line_no = 0
    for line in content.splitlines():
        line_no += 1
        if line.rstrip() in section_kws:
            var_decl = False
        if line.rstrip() in var_kws: # at variable declaration site!
            var_decl = True
            continue
        
        if var_decl:
            spl = line.rstrip().split(": ")
            if len(spl) == 1:
                continue
            var_name = spl[0].rstrip()
            vspl = var_name.split(".")
            if vspl[0] in module_names:
                pass
            else:
                cleaned_var_name = (var_name.replace('.', '_dot_')
                    .replace(':', '_colon_')
                    .replace("\"","_dquote_")
                    .replace('$', '_dollar_')
                    .replace('[', '_lbrack_')
                    .replace(']', '_rbrack_')
                    .replace(r'\\', '_dbs_'))
                if cleaned_var_name == var_name:
                    continue
                else:
                    # print(f"{line_no}: replacing {var_name} with {cleaned_var_name}")
                    # if ret_fc.find(var_name) != -1:
                    #     print(f"{line_no}: FOUND {var_name}")
                    new_ret_fc = ret_fc.replace(var_name, cleaned_var_name)
                    # if ret_fc == new_ret_fc:
                    #     print(f"{line_no}: NO CHANGE")
                    ret_fc = new_ret_fc

    return ret_fc


def preprocess(input_path: Path, do_cpp: bool) -> str:
    """Returns a preprocessed nuXmv model, after running the C-preprocessor (if `do_cpp` is True) and cleaning up identifiers. Returns an empty string on failure.

    1) C Preprocessor Invocation: Since nuXmv admits C-style macros (#ifdef, #include, etc.), we run the file through the C preprocessor
    and obtain a single nuXmv file.

    2) Identifier Cleanup: Identifiers appearing in nuXmv distribution benchmarks do not conform to the identifier grammar specified in the nuXmv reference manual. As such, we replace restricted tokens (`:`, `"`, `\\`, `[`, `]`, `$`) that appear in identifiers with conformant alternatives (usually the written name of the character - `_colon_`, etc.).
    """
    logger.debug(f"Preprocessing {input_path}")

    if do_cpp:
        proc = subprocess.run(["cpp", "-P", str(input_path)], capture_output=True)

        if proc.returncode:
            logger.error(f"C preprocessor failed. Check that 'cpp' is installed and working.")
            return ""
        
        content = proc.stdout.decode("utf-8")
    else:
        with open(str(input_path), 'r') as file:
            content = file.read()

    module_names = get_module_names(content)
    return handle_variables(content, module_names)
