#type: ignore
from sly import Lexer, Parser
from il import *

class ILLexer(Lexer):

    tokens = { NUMERAL, DECIMAL, BINARY,
               SYMBOL, KEYWORD,
               LBRACK, RBRACK, LBRACE, RBRACE, LPAREN, RPAREN,
               RW_UNDERSCORE,
               PK_INPUT, PK_LOCAL, PK_OUTPUT, PK_INIT, PK_TRANS, PK_INV,
               PK_ASSUMPTION, PK_FAIRNESS, PK_REACHABLE, PK_CURRENT, PK_QUERY,
               CMD_DECLARE_SORT, CMD_DEFINE_SORT, CMD_DECLARE_CONST, CMD_DEFINE_FUN, 
               CMD_DECLARE_ENUM_SORT, CMD_DEFINE_SYSTEM, CMD_CHECK_SYSTEM }

    # String containing ignored characters between tokens
    ignore = " \t"
    ignore_comment = r";.*"
    ignore_newline = r"\n+"

    NUMERAL     = r"0|[1-9]\d*"
    DECIMAL     = r"-?\d*\.\d+"
    # HEXADECIMAL = r"#x[A-F0-9]+"
    BINARY      = r"#b[01]+"

    SYMBOL   = r"[a-zA-Z~!@$%^&*_+=<>.?/-][0-9a-zA-Z~!@$%^&*_+=<>.?/-]*'?"
    KEYWORD  = r":" + SYMBOL

    LBRACK = r"\["
    RBRACK = r"\]"
    LBRACE = r"\{"
    RBRACE = r"\}"
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
    SYMBOL["declare-enum"]  = CMD_DECLARE_ENUM_SORT
    SYMBOL["define-system"] = CMD_DEFINE_SYSTEM
    SYMBOL["check-system"]  = CMD_CHECK_SYSTEM

    # Extra action for newlines
    def ignore_newline(self, t):
        self.lineno += t.value.count("\n")

    def error(self, t):
        print(f"{self.lineno}: Illegal character \"%s\" {t.value[0]}")
        self.index += 1


class ILParser(Parser):
    tokens = ILLexer.tokens

    def __init__(self) -> None:
        super().__init__()
        self.input_context = {}
        self.output_context = {}
        self.local_context = {}
        self.logic_context = {}
        self.status = True

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
    
    @_("LPAREN CMD_DEFINE_SORT SYMBOL LPAREN sort_list RPAREN RPAREN")
    def command(self, p):
        return None
    
    @_("LPAREN CMD_DECLARE_CONST SYMBOL sort RPAREN")
    def command(self, p):
        self.logic_context.append((p[2], p[3]))
        return ILDeclareConst(p[2], p[3])
    
    @_("LPAREN CMD_DEFINE_FUN SYMBOL LPAREN sort_list RPAREN RPAREN")
    def command(self, p):
        return None
    
    # @_("LPAREN CMD_DECLARE_ENUM_SORT SYMBOL LPAREN symbol_list RPAREN RPAREN")
    # def command(self, p):
    #     return []
    
    @_("LPAREN CMD_DEFINE_SYSTEM SYMBOL define_system_attribute_list RPAREN")
    def command(self, p):
        if ":input" in p[3]:
            in_vars = p[3][":input"]
            self.input_context = {}
        else:
            in_vars = {}
            
        if ":output" in p[3]:
            out_vars = p[3][":output"]
            self.output_context = {}
        else:
            out_vars = {}

        if ":local" in p[3]:
            local_vars = p[3][":local"]
            self.local_context = {}
        else:
            local_vars = {}
            
        if ":init" in p[3]:
            init_expr = p[3][":init"]
        else:
            init_expr = ILConstant(IL_BOOL_SORT, True)
            
        if ":trans" in p[3]:
            trans_expr = p[3][":trans"]
        else:
            trans_expr = ILConstant(IL_BOOL_SORT, True)
            
        if ":inv" in p[3]:
            inv_expr = p[3][":inv"]
        else:
            inv_expr = ILConstant(IL_BOOL_SORT, True)

        return ILDefineSystem(str(p[2]), in_vars, local_vars, out_vars,
            init_expr, trans_expr, inv_expr)

    @_("LPAREN CMD_CHECK_SYSTEM SYMBOL check_system_attribute_list RPAREN")
    def command(self, p):
        return ILCheckSystem()

    @_("define_system_attribute_list define_system_attribute")
    def define_system_attribute_list(self, p):
        p[0][p[1][0]] = p[1][1]
        return p[0]

    @_("")
    def define_system_attribute_list(self, p):
        return {}

    @_("PK_INPUT LPAREN sorted_var_list RPAREN")
    def define_system_attribute(self, p):
        self.input_context = p[2]
        return (str(p[0]), p[2])

    @_("PK_OUTPUT LPAREN sorted_var_list RPAREN")
    def define_system_attribute(self, p):
        self.output_context = p[2]
        return (str(p[0]), p[2])

    @_("PK_LOCAL LPAREN sorted_var_list RPAREN")
    def define_system_attribute(self, p):
        self.local_context = p[2]
        return (str(p[0]), p[2])

    @_("PK_INIT term",
       "PK_TRANS term",
       "PK_INV term")
    def define_system_attribute(self, p):
        return (str(p[0]), p[1])

    @_("check_system_attribute_list check_system_attribute")
    def check_system_attribute_list(self, p):
        p[0][p[1][0]] = p[1][1]
        return p[0]

    @_("")
    def check_system_attribute_list(self, p):
        return {}

    @_("PK_INPUT LPAREN sorted_var_list RPAREN")
    def check_system_attribute(self, p):
        self.input_context.append(p[2])
        return (str(p[0]), p[2])

    @_("PK_OUTPUT LPAREN sorted_var_list RPAREN")
    def check_system_attribute(self, p):
        self.output_context.append(p[2])
        return (str(p[0]), p[2])

    @_("PK_LOCAL LPAREN sorted_var_list RPAREN")
    def check_system_attribute(self, p):
        self.local_context.append(p[2])
        return (str(p[0]), p[2])

    @_("PK_ASSUMPTION LPAREN SYMBOL term RPAREN",
       "PK_FAIRNESS LPAREN SYMBOL term RPAREN",
       "PK_REACHABLE LPAREN SYMBOL term RPAREN",
       "PK_CURRENT LPAREN SYMBOL term RPAREN")
    def check_system_attribute(self, p):
        return (str(p[0]), p[1])

    @_("PK_QUERY LPAREN SYMBOL LPAREN SYMBOL RPAREN RPAREN")
    def check_system_attribute(self, p):
        return (str(p[0]), p[2])
    
    @_("sorted_var_list LPAREN sorted_var RPAREN")
    def sorted_var_list(self, p):
        # p[0] is a dict, p[2] is a tuple of type (str, ILSort)
        p[0][p[2][0]] = p[2][1]
        return p[0]
    
    @_("")
    def sorted_var_list(self, p):
        return {}
    
    @_("SYMBOL sort")
    def sorted_var(self, p):
        return (p[0], p[1])
    
    @_("term_list term")
    def term_list(self, p):
        p[0].append(p[1])
        return p[0]
    
    @_("")
    def term_list(self, p):
        return []

    @_("identifier")
    def term(self, p):
        if len(p[0].indices) > 0:
            print("Error, variable identifiers must not be indexed.")

        symbol: str = p[0].symbol
        prime: bool = False
        if symbol[len(symbol)-1] == "'":
            prime = True
            symbol = symbol[:-1]

        if symbol in self.input_context:
            if prime:
                print(f"Error: input variable cannot be primed ({symbol}).")
            return ILInputVar(self.input_context[symbol], symbol)

        if symbol in self.output_context:
            return ILOutputVar(self.output_context[symbol], symbol, prime)

        if symbol in self.local_context:
            return ILLocalVar(self.local_context[symbol], symbol, prime)

        for logic_vars in self.logic_context:
            if symbol == logic_vars[0]:
                return ILLocalVar(logic_vars[1], symbol, prime)

        print(f"Error: variable undeclared ({symbol})")

    @_("NUMERAL")
    def term(self, p):
        return ILConstant(IL_NO_SORT, int(p[0]))

    @_("BINARY")
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
        return ILSort(p[0], p[2])

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

