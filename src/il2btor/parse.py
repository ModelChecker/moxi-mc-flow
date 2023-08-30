#type: ignore
if __package__ == "":
    from sly import Lexer, Parser
    from il import *
else:
    from .sly import Lexer, Parser
    from .il import *

class ILLexer(Lexer):

    tokens = { NUMERAL, BINARY, HEXADECIMAL,
               SYMBOL, KEYWORD,
               LPAREN, RPAREN,
               RW_UNDERSCORE,
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

    SYMBOL   = r"[a-zA-Z~!@$%^&*_+=<>.?/-][0-9a-zA-Z~!@$%^&*_+=<>.?/-]*'?"
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
    # SYMBOL["!"]           = RW_BANG
    # SYMBOL["as"]          = RW_AS
    # SYMBOL["let"]         = RW_LET
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
        print(f"{self.lineno}: Illegal character \"%s\" {t.value[0]}")
        self.index += 1


class ILParser(Parser):
    tokens = ILLexer.tokens

    def __init__(self) :
        super().__init__()
        self.status = True
        self.enums = {}

    def error(self, token):
        self.status = False
        return super().error(token)

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
        return ILDeclareSort(p[2], p[3])
    
    @_("LPAREN CMD_DEFINE_SORT SYMBOL LPAREN symbol_list RPAREN sort RPAREN")
    def command(self, p):
        return ILDefineSort(p[2], p[4], p[6])
    
    @_("LPAREN CMD_DECLARE_CONST SYMBOL sort RPAREN")
    def command(self, p):
        return ILDeclareConst(p[2], p[3])
    
    @_("LPAREN CMD_DEFINE_FUN SYMBOL LPAREN sorted_var_list RPAREN sort LPAREN term RPAREN RPAREN")
    def command(self, p):
        return ILDefineFun(p[2], p[4], p[6], p[8])
    
    @_("LPAREN CMD_DECLARE_ENUM_SORT SYMBOL LPAREN symbol_list RPAREN RPAREN")
    def command(self, p):
        values = []
        for value in p[4]:
            values.append(value)
            self.enums[value] = p[2]

        return ILDeclareEnumSort(p[2], values)
    
    @_("LPAREN CMD_DEFINE_SYSTEM SYMBOL define_system_attribute_list RPAREN")
    def command(self, p):
        input, output, local = [], [], []
        init_expr = ILConstant(IL_BOOL_SORT, True)
        trans_expr = ILConstant(IL_BOOL_SORT, True)
        inv_expr = ILConstant(IL_BOOL_SORT, True)
        subsystems = {}

        if ILAttribute.INPUT in p[3]:
            input = p[3][ILAttribute.INPUT]
            
        if ILAttribute.OUTPUT in p[3]:
            output = p[3][ILAttribute.OUTPUT]

        if ILAttribute.LOCAL in p[3]:
            local = p[3][ILAttribute.LOCAL]
            
        if ILAttribute.INIT in p[3]:
            init_expr = p[3][ILAttribute.INIT]
            
        if ILAttribute.TRANS in p[3]:
            trans_expr = p[3][ILAttribute.TRANS]
            
        if ILAttribute.INV in p[3]:
            inv_expr = p[3][ILAttribute.INV]

        if ILAttribute.SUBSYS in p[3]:
            subsystems = p[3][ILAttribute.SUBSYS]

        return ILDefineSystem(str(p[2]), input, output, local, init_expr, trans_expr, inv_expr, subsystems)

    @_("LPAREN CMD_CHECK_SYSTEM SYMBOL check_system_attribute_list RPAREN")
    def command(self, p):
        input, output, local = [], [], []
        assume, fair, reach, current, query = {}, {}, {}, {}, {}

        if ILAttribute.INPUT in p[3]:
            input = p[3][ILAttribute.INPUT]
            
        if ILAttribute.OUTPUT in p[3]:
            output = p[3][ILAttribute.OUTPUT]

        if ILAttribute.LOCAL in p[3]:
            local = p[3][ILAttribute.LOCAL]

        if ILAttribute.ASSUMPTION in p[3]:
            assume = p[3][ILAttribute.ASSUMPTION]
            
        if ILAttribute.FAIRNESS in p[3]:
            fair = p[3][ILAttribute.FAIRNESS]
            
        if ILAttribute.REACHABLE in p[3]:
            reach = p[3][ILAttribute.REACHABLE]
            
        if ILAttribute.CURRENT in p[3]:
            current = p[3][ILAttribute.CURRENT]
            
        if ILAttribute.QUERY in p[3]:
            query = p[3][ILAttribute.QUERY]

        return ILCheckSystem(p[2], input, output, local, assume, fair, reach, current, query)

    @_("LPAREN CMD_EXIT RPAREN")
    def command(self, p):
        return ILExit()

    @_("define_system_attribute_list define_system_attribute")
    def define_system_attribute_list(self, p):
        (attr, value) = p[1]

        if attr not in p[0]:
            p[0][attr] = value
        elif attr.is_definable_once():
            print(f"Error: multiple instances of attribute ({attr.value}).")
            self.status = False
        elif attr.get_value_type() == dict:
            p[0][attr].update(value)
        elif attr.get_value_type() == ILExpr and isinstance(attr, ILAttribute.TRANS):
            p[0][attr] = ILApply(IL_NO_SORT, ILIdentifier("or", []), [p[0][attr], value])
        elif attr.get_value_type() == ILExpr and isinstance(attr, ILAttribute.INV):
            p[0][attr] = ILApply(IL_NO_SORT, ILIdentifier("and", []), [p[0][attr], value])
        else:
            print(f"Error: parser error ({attr.value}).")
            self.status = False

        return p[0]

    @_("")
    def define_system_attribute_list(self, p):
        return {}

    @_("PK_INPUT LPAREN sorted_var_list RPAREN")
    def define_system_attribute(self, p):
        return (ILAttribute.INPUT, p[2])

    @_("PK_OUTPUT LPAREN sorted_var_list RPAREN")
    def define_system_attribute(self, p):
        return (ILAttribute.OUTPUT, p[2])

    @_("PK_LOCAL LPAREN sorted_var_list RPAREN")
    def define_system_attribute(self, p):
        return (ILAttribute.LOCAL, p[2])

    @_("PK_INIT term")
    def define_system_attribute(self, p):
        return (ILAttribute.INIT, p[1])

    @_("PK_TRANS term")
    def define_system_attribute(self, p):
        return (ILAttribute.TRANS, p[1])

    @_("PK_INV term")
    def define_system_attribute(self, p):
        return (ILAttribute.INV, p[1])

    @_("PK_SUBSYS LPAREN SYMBOL LPAREN SYMBOL symbol_list RPAREN RPAREN")
    def define_system_attribute(self, p):
        return (ILAttribute.SUBSYS, {p[2] : (p[4], p[5])})

    @_("check_system_attribute_list check_system_attribute")
    def check_system_attribute_list(self, p):
        (attr, value) = p[1]

        if attr not in p[0]:
            p[0][attr] = value
        elif attr.is_definable_once():
            print(f"Error: multiple instances of attribute '{attr.value}'.")
            self.status = False
        elif attr.get_value_type() == dict:
            p[0][attr].update(value)
        else:
            print(f"Error: parser error ({attr.value}).")
            self.status = False

        return p[0]

    @_("")
    def check_system_attribute_list(self, p):
        return {}

    @_("PK_INPUT LPAREN sorted_var_list RPAREN")
    def check_system_attribute(self, p):
        return (ILAttribute.INPUT, p[2])

    @_("PK_OUTPUT LPAREN sorted_var_list RPAREN")
    def check_system_attribute(self, p):
        return (ILAttribute.OUTPUT, p[2])

    @_("PK_LOCAL LPAREN sorted_var_list RPAREN")
    def check_system_attribute(self, p):
        return (ILAttribute.LOCAL, p[2])

    @_("PK_ASSUMPTION LPAREN SYMBOL term RPAREN")
    def check_system_attribute(self, p):
        return (ILAttribute.ASSUMPTION, {p[2]: p[3]})

    @_("PK_FAIRNESS LPAREN SYMBOL term RPAREN")
    def check_system_attribute(self, p):
        return (ILAttribute.FAIRNESS, {p[2]: p[3]})

    @_("PK_REACHABLE LPAREN SYMBOL term RPAREN")
    def check_system_attribute(self, p):
        return (ILAttribute.REACHABLE, {p[2]: p[3]})

    @_("PK_CURRENT LPAREN SYMBOL term RPAREN")
    def check_system_attribute(self, p):
        return (ILAttribute.CURRENT, {p[2]: p[3]})

    @_("PK_QUERY LPAREN SYMBOL LPAREN symbol_list SYMBOL RPAREN RPAREN")
    def check_system_attribute(self, p):
        p[4].append(p[5])
        return (ILAttribute.QUERY, {p[2]: p[4]})
    
    @_("sorted_var_list LPAREN sorted_var RPAREN")
    def sorted_var_list(self, p):
        p[0].append(p[2])
        return p[0]
    
    @_("")
    def sorted_var_list(self, p):
        return []
    
    @_("SYMBOL sort")
    def sorted_var(self, p):
        return ILVar(ILVarType.NONE, p[1], p[0], False)
    
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

    @_("identifier")
    def term(self, p):
        if len(p[0].indices) > 0:
            print(f"Error, simple term identifiers cannot be indexed ({p[0]}).")
            self.status = False

        symbol: str = p[0].symbol

        if symbol == "True":
            return ILConstant(IL_BOOL_SORT, True)
        elif symbol == "False":
            return ILConstant(IL_BOOL_SORT, False)
        elif symbol in self.enums:
            return ILConstant(IL_ENUM_SORT(self.enums[symbol]), symbol)

        prime: bool = False
        if symbol[len(symbol)-1] == "'":
            prime = True
            symbol = symbol[:-1]

        return ILVar(ILVarType.NONE, IL_NO_SORT, symbol, prime)

    @_("NUMERAL")
    def term(self, p):
        return ILConstant(IL_INT_SORT, int(p[0]))

    @_("HEXADECIMAL") # example: "#x123"
    def term(self, p):
        return ILConstant(IL_BITVEC_SORT(len(p[0][2:])*4), int(p[0][2:], base=16))

    @_("BINARY") # example: "#b101"
    def term(self, p):
        return ILConstant(IL_BITVEC_SORT(len(p[0][2:])), int(p[0][2:], base=2))

    @_("LPAREN identifier term_list term RPAREN")
    def term(self, p):
        p[2].append(p[3])
        return ILApply(IL_NO_SORT, p[1], p[2])

    @_("identifier")
    def sort(self, p):
        return ILSort(p[0], [])

    @_("LPAREN identifier sort_list sort RPAREN")
    def sort(self, p):
        p[2].append(p[3])
        return ILSort(p[1], p[2])

    @_("sort_list sort")
    def sort_list(self, p):
        p[0].append(p[1])
        return p[0]

    @_("")
    def sort_list(self, p):
        return []

    # Identifiers
    @_("SYMBOL")
    def identifier(self, p):
        return ILIdentifier(p[0], [])

    @_("LPAREN RW_UNDERSCORE SYMBOL index_list index RPAREN")
    def identifier(self, p):
        p[3].append(p[4])
        return ILIdentifier(p[2], p[3])

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


def parse(input: str) -> Optional[ILProgram]:
    """Parse contents of input and returns corresponding program on success, else returns None."""
    lexer: ILLexer = ILLexer()
    parser: ILParser = ILParser()
    cmds = parser.parse(lexer.tokenize(input))
    return ILProgram(cmds) if not cmds == None else None