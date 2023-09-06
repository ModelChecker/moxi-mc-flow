#type: ignore
import sys

if __package__ == "":
    from sly import Lexer, Parser
    from btor_witness import *
else:
    from .sly import Lexer, Parser
    from .btor_witness import *

class BtorWitnessLexer(Lexer):

    tokens = { NEWLINE, UINT, BINARY_STRING, SYMBOL, LBRACK, RBRACK, 
               RW_DOT, RW_AT, RW_HASH, RW_b, RW_j, RW_sat }

    # String containing ignored characters between tokens
    ignore = r" "
    ignore_comment = r";.*\n"

    NEWLINE = r"\n"

    UINT = r"0|([1-9]\d*)"
    BINARY_STRING = r"[01]+"

    SYMBOL   = r"[a-zA-Z~!@$%^&*_+=<>.?/-][0-9a-zA-Z~!@$%^&*_+=<>.?/-]*"

    LBRACK = r"\["
    RBRACK = r"\]"

    # Reserved keywords
    SYMBOL["."] = RW_DOT
    SYMBOL["@"] = RW_AT
    SYMBOL["#"] = RW_HASH
    SYMBOL["b"] = RW_b
    SYMBOL["j"] = RW_j
    SYMBOL["sat"] = RW_sat

    # Extra action for newlines
    def ignore_newline(self, t):
        self.lineno += t.value.count("\n")

    def error(self, t):
        sys.stderr.write(f"{self.lineno}: Illegal character \"%s\" {t.value[0]}")
        self.index += 1


class BtorWitnessParser(Parser):
    tokens = BtorWitnessLexer.tokens

    def __init__(self):
        super().__init__()
        self.status = True
        self.enums = {}

    def error(self, token):
        self.status = False
        sys.stderr.write(f"Error: Unexpected token ({token})")

    @_("header frame_list frame NEWLINE DOT")
    def witness(self, p):
        p[1].append(p[2])
        return p[1]

    @_("sat NEWLINE RW_b UINT")
    def header(self, p):
        return []

    @_("sat NEWLINE RW_j UINT")
    def header(self, p):
        return []

    @_("frame_list frame")
    def frame_list(self, p):
        p[0].append(p[1])
        return p[0]

    @_("")
    def frame_list(self, p):
        return []

    @_("state_part input_part")
    def frame(self, p):
        return []

    @_("input_part")
    def frame(self, p):
        return []

    @_("RW_HASH UINT NEWLINE model")
    def state_part(self, p):
        return []

    @_("RW_AT UINT NEWLINE model")
    def input_part(self, p):
        return []

    @_("model assignment NEWLINE")
    def model(self, p):
        return []

    @_("")
    def model(self, p):
        return []

    @_("UINT BINARY_STRING SYMBOL")
    def assignment(self, p):
        return []

    @_("UINT BINARY_STRING")
    def assignment(self, p):
        return []

    @_("UINT LBRACK BINARY_STRING RBRACK BINARY_STRING")
    def assignment(self, p):
        return []


def parse(input: str) -> Optional[ILProgram]:
    """Parse contents of input and returns corresponding program on success, else returns None."""
    lexer: BtorWitnessLexer = BtorWitnessLexer()
    parser: BtorWitnessParser = BtorWitnessParser()
    cmds = parser.parse(lexer.tokenize(input))

    if parser.status and cmds:
        return ILProgram(cmds)
    return None