#type: ignore
import sys

from .sly import Lexer, Parser
from .btor_witness import *

class BtorWitnessLexer(Lexer):

    tokens = { NEWLINE, NUMBER, SYMBOL, LBRACK, RBRACK, STAR,
               STATE_HEADER, INPUT_HEADER, BAD_PROP, JUSTICE_PROP, 
               RW_DOT, RW_SAT }

    # String containing ignored characters between tokens
    ignore = r" "
    ignore_comment = r";.*\n"

    NEWLINE = r"\n"

    # NUMBER = r"([01]+)|0|([1-9]\d*)" # token for both binary strings and uints
    NUMBER = r"\d+"

    STATE_HEADER = r"#(0|([1-9]\d*))"
    INPUT_HEADER = r"@(0|([1-9]\d*))"

    BAD_PROP = r"b(0|([1-9]\d*))"
    JUSTICE_PROP = r"j(0|([1-9]\d*))"

    LBRACK = r"\["
    RBRACK = r"\]"
    STAR   = r"\*"

    SYMBOL = r"[a-zA-Z~!@$%^&*_+=<>.?/-:#|[\]][0-9a-zA-Z~!@$%^&*_+=<>.?/-:#|[\]]*"

    # Reserved keywords
    SYMBOL["."] = RW_DOT
    SYMBOL["sat"] = RW_SAT

    # Extra action for newlines
    def NEWLINE(self, t):
        self.lineno += t.value.count("\n")
        return t

    def error(self, t):
        sys.stderr.write(f"{self.lineno}: Illegal character \"%s\" {t.value[0]}\n")
        self.index += 1


class BtorWitnessParser(Parser):
    tokens = BtorWitnessLexer.tokens

    def __init__(self):
        super().__init__()
        self.status = True
        self.enums = {}

    def error(self, token):
        self.status = False
        sys.stderr.write(f"Error: Unexpected token ({token})\n")

    @_("header frame frame_list RW_DOT NEWLINE")
    def witness(self, p):
        bad_props = []
        justice_props = []
        for prop in p[0]:
            is_bad_prop, prop_idx = prop
            if is_bad_prop:
                bad_props.append(prop_idx)
            else:
                justice_props.append(prop_idx)

        frames = [p[1]] + p[2]

        return BtorWitness(bad_props, justice_props, frames)

    @_("RW_SAT NEWLINE prop_list NEWLINE")
    def header(self, p):
        return p[2]

    @_("prop_list BAD_PROP")
    def prop_list(self, p):
        p[0].append((True, int(p[1][1:])))
        return p[0]

    @_("prop_list JUSTICE_PROP")
    def prop_list(self, p):
        p[0].append((False, int(p[1][1:])))
        return p[0]

    @_("")
    def prop_list(self, p):
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
        idx, state_part = p[0]
        _, input_part = p[1]
        return BtorFrame(idx, state_part, input_part)

    @_("input_part")
    def frame(self, p):
        idx, input_part = p[0]
        return BtorFrame(idx, [], input_part)

    @_("STATE_HEADER NEWLINE model")
    def state_part(self, p):
        return (int(p[0][1:]), p[2])

    @_("INPUT_HEADER NEWLINE model")
    def input_part(self, p):
        return (int(p[0][1:]), p[2])

    @_("model assignment NEWLINE")
    def model(self, p):
        p[0].append(p[1])
        return p[0]

    @_("")
    def model(self, p):
        return []

    @_("NUMBER binary_string SYMBOL")
    def assignment(self, p):
        return BtorBitVecAssignment(int(p[0]), p[1], p[2])

    @_("NUMBER binary_string")
    def assignment(self, p):
        return BtorBitVecAssignment(int(p[0]), p[1], None)

    @_("NUMBER LBRACK binary_string RBRACK binary_string SYMBOL")
    def assignment(self, p):
        return BtorArrayAssignment(int(p[0]), (p[2], p[4]), p[5])

    @_("NUMBER LBRACK binary_string RBRACK binary_string")
    def assignment(self, p):
        return BtorArrayAssignment(int(p[0]), (p[2], p[4]), None)

    @_("NUMBER LBRACK STAR RBRACK binary_string SYMBOL")
    def assignment(self, p):
        return BtorArrayAssignment(int(p[0]), (None, p[4]), p[5])

    @_("NUMBER LBRACK STAR RBRACK binary_string")
    def assignment(self, p):
        return BtorArrayAssignment(int(p[0]), (None, p[4]), None)

    @_("NUMBER")
    def binary_string(self, p):
        return BitVec(len(p[0]), int(p[0], base=2))


def parse_witness(input: str) -> Optional[BtorWitness]:
    """Parse contents of input and returns corresponding program on success, else returns None."""
    lexer: BtorWitnessLexer = BtorWitnessLexer()
    parser: BtorWitnessParser = BtorWitnessParser()
    witness = parser.parse(lexer.tokenize(input))

    return witness if parser.status else None