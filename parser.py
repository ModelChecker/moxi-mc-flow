#type: ignore
from .sly import Lexer, Parser
from il import *


class ILLexer(Lexer):

    tokens = { NUMERAL, DECIMAL EQUAL, SYMBOL, FLOAT, INT, SEMI, COLON, DOT, COMMA, QUEST,
               LBRACK, RBRACK, LBRACE, RBRACE, LPAREN, RPAREN,
               CMD_DECLARE_SORT, CMD_DEFINE_SORT, CMD_DECLARE_CONST, CMD_DEFINE_FUN, 
               CMD_DECLARE_ENUM_SORT, CMD_DEFINE_SYSTEM, CMD_CHECK_SYSTEM, }

    # String containing ignored characters between tokens
    ignore = " \t"
    ignore_comment = r";.*"
    ignore_newline = r"\n+"

    NUMERAL = r"0|[1-9]\d*"
    DECIMAL = r"-?\d*\.\d+"

    # Others
    EQUAL  = r"="
    SYMBOL  = r"[a-zA-Z_][a-zA-Z0-9_]*"
    QUEST   = r"\?"
    SEMI    = r";"
    COLON   = r":"
    DOT     = r"\."
    COMMA   = r","
    LBRACK  = r"\["
    RBRACK  = r"\]"
    LBRACE  = r"\{"
    RBRACE  = r"\}"
    LPAREN  = r"\("
    RPAREN  = r"\)"
    PRIME   = r"'"

    SYMBOL["declare-sort"]  = CMD_DECLARE_SORT
    SYMBOL["define-sort"]   = CMD_DEFINE_SORT
    SYMBOL["declare-const"] = CMD_DECLARE_CONST
    SYMBOL["define-fun"]    = CMD_DEFINE_FUN
    SYMBOL["declare-enum"]  = CMD_DECLARE_ENUM_SORT
    SYMBOL["define-system"] = CMD_DEFINE_SYSTEM
    SYMBOL["check-system"]  = CMD_CHECK_SYSTEM

    SYMBOL[":input"]  = ATTR_INPUT
    SYMBOL[":local"]  = ATTR_LOCAL
    SYMBOL[":output"] = ATTR_OUTPUT
    SYMBOL[":init"]   = ATTR_INIT
    SYMBOL[":trans"]  = ATTR_TRANS
    SYMBOL[":inv"]    = ATTR_INV

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
        self.sorts = {}
        self.vars = {}
        self.status = True

        self.sorts["Bool"] = 0
        self.sorts["BitVec"] = 1
        self.sorts["Array"] = 2

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
    
    # @_("LPAREN CMD_DEFINE_SORT SYMBOL _ RPAREN")
    # def command(self, p):
    #     return []
    
    @_("LPAREN CMD_DECLARE_CONST SYMBOL sort RPAREN")
    def command(self, p):
        return ILDeclareConst(p[2], p[3])
    
    # @_("LPAREN CMD_DEFINE_FUN SYMBOL _ RPAREN")
    # def command(self, p):
    #     return []
    
    # @_("LPAREN CMD_DECLARE_ENUM_SORT SYMBOL LPAREN symbol_list RPAREN RPAREN")
    # def command(self, p):
    #     return []
    
    @_("LPAREN CMD_DEFINE_SYSTEM SYMBOL define_system_attribute_list RPAREN")
    def command(self, p):
        if "input" in p[3]:
            in_vars = p[3]["input"]
        else:
            in_vars = {}

        if "local" in p[3]:
            local_vars = p[3]["local"]
        else:
            local_vars = {}
            
        if "output" in p[3]:
            out_vars = p[3]["output"]
        else:
            out_vars = {}
            
        if "init" in p[3]:
            init_expr = p[3]["init"]
        else:
            init_expr = ILConstant(IL_BOOL_SORT, True)
            
        if "trans" in p[3]:
            trans_expr = p[3]["trans"]
        else:
            trans_expr = ILConstant(IL_BOOL_SORT, True)
            
        if "inv" in p[3]:
            inv_expr = p[3]["inv"]
        else:
            inv_expr = ILConstant(IL_BOOL_SORT, True)

        return ILDefineSystem(str(p[2]), in_vars, local_vars, out_vars,
            init_expr, trans_expr, inv_expr)

    @_("define_system_attribute_list define_system_attribute")
    def define_system_attribute_list(self, p):
        p[0][p[1][0]] = p[1][1]
        return p[0]

    @_("")
    def define_system_attribute_list(self, p):
        return {}

    @_("ATTR_INPUT LPAREN sorted_var_list RPAREN",
       "ATTR_LOCAL LPAREN sorted_var_list RPAREN",
       "ATTR_OUTPUT LPAREN sorted_var_list RPAREN")
    def define_system_attribute(self, p):
        return (str(p[1]), p[3])

    @_("ATTR_INIT LPAREN term RPAREN",
       "ATTR_TRANS LPAREN term RPAREN",
       "ATTR_INV LPAREN term RPAREN")
    def define_system_attribute(self, p):
        return (str(p[1]), p[3])
    
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
    
    @_("term_list LPAREN term RPAREN")
    def term_list(self, p):
        p[0].append(p[2])
        return p[0]
    
    @_("")
    def term_list(self, p):
        return []

    @_("identifier")
    def term(self, p):
        # term is a variable, sort and prime will be resolved during type checking
        return ILVar(p[0].symbol, IL_NO_SORT, False)

    @_("identifier term_list term")
    def term(self, p):
        p[1].append(p[2])
        return ILApply(p[0], p[1])

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

    @_("LPAREN UNDERSCORE SYMBOL index_list index RPAREN")
    def identifier(self, p):
        indices = p[3].append(p[4])
        return ILIdentifier(p[2], indices)

    # Indices
    @_("index_list index")
    def index_list(self, p):
        p[0].append(p[1])
        return p[0]

    @_("")
    def index_list(self, p):
        return []

    @_("SYMBOL")
    def index(self, p):
        return p[0]

    @_("NUMERAL")
    def index(self, p):
        return int(p[0])

