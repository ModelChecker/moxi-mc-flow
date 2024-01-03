#type: ignore
import sys

from .sly import Lexer, Parser
from .mcil import *
from .btor_witness import *

class MCILLexer(Lexer):

    tokens = { NUMERAL, BINARY, HEXADECIMAL,
               SYMBOL, KEYWORD,
               LPAREN, RPAREN,
               RW_UNDERSCORE, RW_LET, RW_AS,
               PK_INPUT, PK_LOCAL, PK_OUTPUT, PK_INIT, PK_TRANS, PK_INV, PK_SUBSYS,
               PK_ASSUMPTION, PK_FAIRNESS, PK_REACHABLE, PK_CURRENT, PK_QUERY,
               CMD_DECLARE_SORT, CMD_DEFINE_SORT, CMD_DECLARE_CONST, CMD_DEFINE_FUN, 
               CMD_DECLARE_ENUM_SORT, CMD_DEFINE_SYSTEM, CMD_CHECK_SYSTEM, CMD_EXIT }

    # String containing ignored characters between tokens
    ignore = " \t"
    ignore_comment = r";.*"
    ignore_newline = r"\n+"

    NUMERAL     = r"0|[1-9]\d*"
    # DECIMAL     = r"-?\d*\.\d+"
    HEXADECIMAL = r"#x[A-F0-9]+"
    BINARY      = r"#b[01]+"

    SYMBOL   = r"[a-zA-Z~!@$%^&*_+=<>.?/-][0-9a-zA-Z~!@#$%^&*_+=<>.?/-]*'?"
    KEYWORD  = r":" + SYMBOL

    # LBRACK = r"\["
    # RBRACK = r"\]"
    # LBRACE = r"\{"
    # RBRACE = r"\}"
    LPAREN = r"\("
    RPAREN = r"\)"

    # Reserved keywords
    # SYMBOL["BINARY"]      = RW_BINARY
    # SYMBOL["DECIMAL"]     = RW_DECIMAL
    # SYMBOL["HEXADECIMAL"] = RW_HEXADECIMAL
    # SYMBOL["NUMERAL"]     = RW_NUMERAL
    # SYMBOL["STRING"]      = RW_STRING
    SYMBOL["_"]           = RW_UNDERSCORE
    SYMBOL["let"]         = RW_LET
    # SYMBOL["!"]           = RW_BANG
    SYMBOL["as"]          = RW_AS
    # SYMBOL["exists"]      = RW_EXISTS
    # SYMBOL["forall"]      = RW_FORALL
    # SYMBOL["match"]       = RW_MATCH
    # SYMBOL["par"]         = RW_PAR

    # Predefined keywords
    KEYWORD[":input"]  = PK_INPUT
    KEYWORD[":local"]  = PK_LOCAL
    KEYWORD[":output"] = PK_OUTPUT
    KEYWORD[":init"]   = PK_INIT
    KEYWORD[":trans"]  = PK_TRANS
    KEYWORD[":inv"]    = PK_INV
    KEYWORD[":subsys"]    = PK_SUBSYS
    KEYWORD[":assumption"] = PK_ASSUMPTION
    KEYWORD[":fairness"]   = PK_FAIRNESS
    KEYWORD[":reachable"]  = PK_REACHABLE
    KEYWORD[":current"]    = PK_CURRENT
    KEYWORD[":query"]      = PK_QUERY

    # Command names
    SYMBOL["declare-sort"]  = CMD_DECLARE_SORT
    SYMBOL["define-sort"]   = CMD_DEFINE_SORT
    SYMBOL["declare-const"] = CMD_DECLARE_CONST
    SYMBOL["define-fun"]    = CMD_DEFINE_FUN
    SYMBOL["declare-enum-sort"]  = CMD_DECLARE_ENUM_SORT
    SYMBOL["define-system"] = CMD_DEFINE_SYSTEM
    SYMBOL["check-system"]  = CMD_CHECK_SYSTEM
    SYMBOL["exit"]  = CMD_EXIT

    # Extra action for newlines
    def ignore_newline(self, t):
        self.lineno += t.value.count("\n")

    def error(self, t):
        sys.stderr.write(f"{self.lineno}: Illegal character \"%s\" {t.value[0]}\n")
        self.index += 1


class MCILParser(Parser):
    tokens = MCILLexer.tokens

    def __init__(self) :
        super().__init__()
        self.status = True
        self.enums = {}

    def error(self, token):
        self.status = False
        sys.stderr.write(f"Error:{token.lineno}: Unexpected token ({token})\n")

    @_("command_list command")
    def command_list(self, p):
        if p[1]:
            p[0].append(p[1])
        return p[0]

    @_("")
    def command_list(self, p):
        return []

    @_("LPAREN CMD_DECLARE_SORT SYMBOL NUMERAL RPAREN")
    def command(self, p):
        return MCILDeclareSort(p[2], p[3])
    
    @_("LPAREN CMD_DEFINE_SORT SYMBOL LPAREN symbol_list RPAREN sort RPAREN")
    def command(self, p):
        return MCILDefineSort(p[2], p[4], p[6])
    
    @_("LPAREN CMD_DECLARE_CONST SYMBOL sort RPAREN")
    def command(self, p):
        return MCILDeclareConst(p[2], p[3])
    
    @_("LPAREN CMD_DEFINE_FUN SYMBOL LPAREN sorted_var_list RPAREN sort term RPAREN")
    def command(self, p):
        return MCILDefineFun(p[2], p[4], p[6], p[7])
    
    @_("LPAREN CMD_DECLARE_ENUM_SORT SYMBOL LPAREN symbol_list RPAREN RPAREN")
    def command(self, p):
        values = []
        for value in p[4]:
            values.append(value)
            self.enums[value] = p[2]

        return MCILDeclareEnumSort(p[2], values)
    
    @_("LPAREN CMD_DEFINE_SYSTEM SYMBOL define_system_attribute_list RPAREN")
    def command(self, p):
        input, output, local = [], [], []
        init_expr = MCILConstant(MCIL_BOOL_SORT, True)
        trans_expr = MCILConstant(MCIL_BOOL_SORT, True)
        inv_expr = MCILConstant(MCIL_BOOL_SORT, True)
        subsystems = {}

        if MCILAttribute.INPUT in p[3]:
            input = p[3][MCILAttribute.INPUT]
            
        if MCILAttribute.OUTPUT in p[3]:
            output = p[3][MCILAttribute.OUTPUT]

        if MCILAttribute.LOCAL in p[3]:
            local = p[3][MCILAttribute.LOCAL]
            
        if MCILAttribute.INIT in p[3]:
            init_expr = p[3][MCILAttribute.INIT]
            
        if MCILAttribute.TRANS in p[3]:
            trans_expr = p[3][MCILAttribute.TRANS]
            
        if MCILAttribute.INV in p[3]:
            inv_expr = p[3][MCILAttribute.INV]

        if MCILAttribute.SUBSYS in p[3]:
            subsystems = p[3][MCILAttribute.SUBSYS]

        return MCILDefineSystem(str(p[2]), input, output, local, init_expr, trans_expr, inv_expr, subsystems)

    @_("LPAREN CMD_CHECK_SYSTEM SYMBOL check_system_attribute_list RPAREN")
    def command(self, p):
        input, output, local = [], [], []
        assume, fair, reach, current, query = {}, {}, {}, {}, {}

        if MCILAttribute.INPUT in p[3]:
            input = p[3][MCILAttribute.INPUT]
            
        if MCILAttribute.OUTPUT in p[3]:
            output = p[3][MCILAttribute.OUTPUT]

        if MCILAttribute.LOCAL in p[3]:
            local = p[3][MCILAttribute.LOCAL]

        if MCILAttribute.ASSUMPTION in p[3]:
            assume = p[3][MCILAttribute.ASSUMPTION]
            
        if MCILAttribute.FAIRNESS in p[3]:
            fair = p[3][MCILAttribute.FAIRNESS]
            
        if MCILAttribute.REACHABLE in p[3]:
            reach = p[3][MCILAttribute.REACHABLE]
            
        if MCILAttribute.CURRENT in p[3]:
            current = p[3][MCILAttribute.CURRENT]
            
        if MCILAttribute.QUERY in p[3]:
            query = p[3][MCILAttribute.QUERY]

        return MCILCheckSystem(p[2], input, output, local, assume, fair, reach, current, query)

    @_("LPAREN CMD_EXIT RPAREN")
    def command(self, p):
        return MCILExit()

    @_("define_system_attribute_list define_system_attribute")
    def define_system_attribute_list(self, p):
        (attr, value) = p[1]

        if attr not in p[0]:
            p[0][attr] = value
        elif attr.is_definable_once():
            sys.stderr.write(f"Error:{p.lineno}: multiple instances of attribute ({attr.value}).")
            self.status = False
        elif attr.get_value_type() == dict:
            p[0][attr].update(value)
        elif attr.get_value_type() == MCILExpr and isinstance(attr, MCILAttribute.TRANS):
            p[0][attr] = MCILApply(MCIL_NO_SORT, MCILIdentifier("or", []), [p[0][attr], value])
        elif attr.get_value_type() == MCILExpr and isinstance(attr, MCILAttribute.INV):
            p[0][attr] = MCILApply(MCIL_NO_SORT, MCILIdentifier("and", []), [p[0][attr], value])
        else:
            sys.stderr.write(f"Error:{p.lineno}: parser error ({attr.value}).")
            self.status = False

        return p[0]

    @_("")
    def define_system_attribute_list(self, p):
        return {}

    @_("PK_INPUT LPAREN sorted_var_list RPAREN")
    def define_system_attribute(self, p):
        return (MCILAttribute.INPUT, p[2])

    @_("PK_OUTPUT LPAREN sorted_var_list RPAREN")
    def define_system_attribute(self, p):
        return (MCILAttribute.OUTPUT, p[2])

    @_("PK_LOCAL LPAREN sorted_var_list RPAREN")
    def define_system_attribute(self, p):
        return (MCILAttribute.LOCAL, p[2])

    @_("PK_INIT term")
    def define_system_attribute(self, p):
        return (MCILAttribute.INIT, p[1])

    @_("PK_TRANS term")
    def define_system_attribute(self, p):
        return (MCILAttribute.TRANS, p[1])

    @_("PK_INV term")
    def define_system_attribute(self, p):
        return (MCILAttribute.INV, p[1])

    @_("PK_SUBSYS LPAREN SYMBOL LPAREN SYMBOL symbol_list RPAREN RPAREN")
    def define_system_attribute(self, p):
        return (MCILAttribute.SUBSYS, {p[2] : (p[4], p[5])})

    @_("check_system_attribute_list check_system_attribute")
    def check_system_attribute_list(self, p):
        (attr, value) = p[1]

        if attr not in p[0]:
            p[0][attr] = value
        elif attr.is_definable_once():
            sys.stderr.write(f"Error:{p.lineno}: multiple instances of attribute '{attr.value}'.\n")
            self.status = False
        elif attr.get_value_type() == dict:
            # check for duplicate symbols
            if [v for v in value.keys() if v in p[0][attr]]:
                sys.stderr.write(f"Error:{p.lineno}: repeat symbol for attribute '{attr.value}'.\n")
                self.status = False
            p[0][attr].update(value)
        else:
            sys.stderr.write(f"Error:{p.lineno}: parser error ({attr.value}).\n")
            self.status = False

        return p[0]

    @_("")
    def check_system_attribute_list(self, p):
        return {}

    @_("PK_INPUT LPAREN sorted_var_list RPAREN")
    def check_system_attribute(self, p):
        return (MCILAttribute.INPUT, p[2])

    @_("PK_OUTPUT LPAREN sorted_var_list RPAREN")
    def check_system_attribute(self, p):
        return (MCILAttribute.OUTPUT, p[2])

    @_("PK_LOCAL LPAREN sorted_var_list RPAREN")
    def check_system_attribute(self, p):
        return (MCILAttribute.LOCAL, p[2])

    @_("PK_ASSUMPTION LPAREN SYMBOL term RPAREN")
    def check_system_attribute(self, p):
        return (MCILAttribute.ASSUMPTION, {p[2]: p[3]})

    @_("PK_FAIRNESS LPAREN SYMBOL term RPAREN")
    def check_system_attribute(self, p):
        return (MCILAttribute.FAIRNESS, {p[2]: p[3]})

    @_("PK_REACHABLE LPAREN SYMBOL term RPAREN")
    def check_system_attribute(self, p):
        return (MCILAttribute.REACHABLE, {p[2]: p[3]})

    @_("PK_CURRENT LPAREN SYMBOL term RPAREN")
    def check_system_attribute(self, p):
        return (MCILAttribute.CURRENT, {p[2]: p[3]})

    @_("PK_QUERY LPAREN SYMBOL LPAREN symbol_list SYMBOL RPAREN RPAREN")
    def check_system_attribute(self, p):
        p[4].append(p[5])
        return (MCILAttribute.QUERY, {p[2]: p[4]})
    
    @_("sorted_var_list LPAREN sorted_var RPAREN")
    def sorted_var_list(self, p):
        p[0].append(p[2])
        return p[0]
    
    @_("")
    def sorted_var_list(self, p):
        return []
    
    @_("SYMBOL sort")
    def sorted_var(self, p):
        return MCILVar(MCILVarType.NONE, p[1], p[0], False)
    
    @_("term_list term")
    def term_list(self, p):
        p[0].append(p[1])
        return p[0]
    
    @_("")
    def term_list(self, p):
        return []

    @_("symbol_list SYMBOL")
    def symbol_list(self, p):
        p[0].append(p[1])
        return p[0]

    @_("")
    def symbol_list(self, p):
        return []

    @_("bound_var_list LPAREN SYMBOL term RPAREN")
    def bound_var_list(self, p):
        p[0].append((p[2], p[3]))
        return p[0]

    @_("")
    def bound_var_list(self, p):
        return []

    @_("identifier")
    def term(self, p):
        if len(p[0].indices) > 0:
            sys.stderr.write(f"Error, simple term identifiers cannot be indexed ({p[0]}).")
            self.status = False

        symbol: str = p[0].symbol
        if symbol == "true":
            return MCILConstant(MCIL_BOOL_SORT, True)
        elif symbol == "false":
            return MCILConstant(MCIL_BOOL_SORT, False)
        elif symbol in self.enums:
            return MCILConstant(MCIL_ENUM_SORT(self.enums[symbol]), symbol)

        prime: bool = False
        if symbol[len(symbol)-1] == "'":
            prime = True
            symbol = symbol[:-1]

        return MCILVar(MCILVarType.NONE, MCIL_NO_SORT, symbol, prime)

    @_("NUMERAL")
    def term(self, p):
        return MCILConstant(MCIL_INT_SORT, int(p[0]))

    @_("HEXADECIMAL") # example: "#x123"
    def term(self, p):
        return MCILConstant(MCIL_BITVEC_SORT(len(p[0][2:])*4), int(p[0][2:], base=16))

    @_("BINARY") # example: "#b101"
    def term(self, p):
        return MCILConstant(MCIL_BITVEC_SORT(len(p[0][2:])), int(p[0][2:], base=2))

    @_("LPAREN identifier term_list term RPAREN")
    def term(self, p):
        p[2].append(p[3])
        return MCILApply(MCIL_NO_SORT, p[1], p[2])

    @_("LPAREN RW_LET LPAREN bound_var_list RPAREN term RPAREN")
    def term(self, p):
        return MCILLetExpr(MCIL_NO_SORT, p[3], p[5])

    @_("LPAREN qualified_identifier term RPAREN")
    def term(self, p):
        ident, sort = p[1]
        return MCILApply(sort, ident, [p[2]])

    @_("LPAREN term RPAREN")
    def term(self, p):
        return p[1]

    @_("identifier")
    def sort(self, p):
        return MCILSort(p[0], [])

    @_("LPAREN identifier sort_list sort RPAREN")
    def sort(self, p):
        p[2].append(p[3])
        return MCILSort(p[1], p[2])

    @_("sort_list sort")
    def sort_list(self, p):
        p[0].append(p[1])
        return p[0]

    @_("")
    def sort_list(self, p):
        return []

    @_("RW_AS identifier sort")
    def qualified_identifier(self, p):
        return (p[1], p[2])

    # Identifiers
    @_("SYMBOL")
    def identifier(self, p):
        return MCILIdentifier(p[0], [])

    @_("LPAREN RW_UNDERSCORE SYMBOL index_list index RPAREN")
    def identifier(self, p):
        p[3].append(p[4])
        return MCILIdentifier(p[2], p[3])

    # Indices
    @_("index_list index")
    def index_list(self, p):
        p[0].append(p[1])
        return p[0]

    @_("")
    def index_list(self, p):
        return []

    @_("NUMERAL")
    def index(self, p):
        return int(p[0])


def parse_mcil(input: str) -> Optional[MCILProgram]:
    """Parse contents of input and returns corresponding program on success, else returns None."""
    lexer: MCILLexer = MCILLexer()
    parser: MCILParser = MCILParser()
    cmds = parser.parse(lexer.tokenize(input))

    if parser.status and cmds:
        return MCILProgram(cmds)
    return None


class BtorWitnessLexer(Lexer):

    tokens = { NEWLINE, NUMBER, SYMBOL, LBRACK, RBRACK, 
               STATE_HEADER, INPUT_HEADER, BAD_PROP, JUSTICE_PROP, RW_DOT, RW_SAT }

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

    SYMBOL = r"[a-zA-Z~!@$%^&*_+=<>.?/-:#[\]][0-9a-zA-Z~!@$%^&*_+=<>.?/-:#[\]]*"

    # Reserved keywords
    SYMBOL["."] = RW_DOT
    SYMBOL["sat"] = RW_SAT

    # Extra action for newlines
    def NEWLINE(self, t):
        self.lineno += t.value.count("\n")
        return t

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

    @_("NUMBER")
    def binary_string(self, p):
        return BitVec(len(p[0]), int(p[0], base=2))


def parse_witness(input: str) -> Optional[BtorWitness]:
    """Parse contents of input and returns corresponding program on success, else returns None."""
    lexer: BtorWitnessLexer = BtorWitnessLexer()
    parser: BtorWitnessParser = BtorWitnessParser()
    witness = parser.parse(lexer.tokenize(input))

    return witness if parser.status else None