import pathlib
import subprocess

from src import log

FILE_NAME = pathlib.Path(__file__).name

var_kws = {"IVAR", "VAR", "FROZENVAR"}

section_kws = {
    "VAR",
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
    "PSLSPEC",
}


def handle_variables(content: str):
    var_decl = False

    ret_fc = content
    line_no = 0
    for line in content.splitlines():
        line_no += 1
        if len(line) < 1:
            continue
        if line.split()[0].rstrip() in section_kws:
            var_decl = False
        if line.rstrip() in var_kws:  # at variable declaration site!
            var_decl = True
            continue

        if var_decl:
            spl = line.rstrip().split(": ")
            if len(spl) == 1:
                continue
            var_name = spl[0].strip()

            if (
                any([c in var_name for c in {'.',':','$','[',']','\\\\'}])
            ):
                cleaned_var_name = (
                    var_name.replace(".", "__dot__")
                    .replace(":", "__colon__")
                    .replace('"', "__dquote__")
                    .replace("$", "__dollar__")
                    .replace("[", "__lbrack__")
                    .replace("]", "__rbrack__")
                    .replace("\\\\", "__dbs__")
                )
                if cleaned_var_name == var_name:
                    continue
                else:
                    new_ret_fc = ret_fc.replace(var_name, cleaned_var_name)
                    ret_fc = new_ret_fc

    return ret_fc


def preprocess(input_path: pathlib.Path, do_cpp: bool) -> str:
    """Returns a preprocessed nuXmv model, after running the C-preprocessor (if `do_cpp` is True) and cleaning up identifiers. Returns an empty string on failure.

    1) C Preprocessor Invocation: Since nuXmv admits C-style macros (#ifdef, #include, etc.), we run the file through the C preprocessor
    and obtain a single nuXmv file.

    2) Identifier Cleanup: Identifiers appearing in nuXmv distribution benchmarks do not conform to the identifier grammar specified in the nuXmv reference manual. As such, we escape most identifiers with quotes, which are equivalently escaped with pipes in MoXI.
    """
    log.debug(2, f"Preprocessing {input_path}", FILE_NAME)

    if do_cpp:
        proc = subprocess.run(["cpp", "-P", str(input_path)], capture_output=True)

        if proc.returncode:
            log.error(
                "C preprocessor failed. Check that 'cpp' is installed and working.",
                FILE_NAME,
            )
            return ""

        content = proc.stdout.decode("utf-8")
    else:
        with open(str(input_path), "r") as file:
            content = file.read()

    return handle_variables(content)