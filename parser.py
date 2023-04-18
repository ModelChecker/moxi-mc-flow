#type: ignore

from .sly import Lexer, Parser
from il import *


class ILLexer(Lexer):

    tokens = { CMD_DECLARE_SORT, CMD_DEFINE_SORT, CMD_DECLARE_CONST, CMD_DEFINE_FUN, 
               CMD_DECLARE_ENUM_SORT, CMD_DEFINE_SYSTEM, CMD_CHECK_SYSTEM,
               EQUAL, SYMBOL, NUM, FLOAT, INT, SEMI, COLON, DOT, COMMA, QUEST,
               LBRACK, RBRACK, LBRACE, RBRACE, LPAREN, RPAREN }

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

    SYMBOL["declare-sort"] = CMD_DECLARE_SORT
    SYMBOL["define-sort"] = CMD_DEFINE_SORT
    SYMBOL["declare-const"] = CMD_DECLARE_CONST
    SYMBOL["define-fun"] = CMD_DEFINE_FUN
    SYMBOL["declare-enum"] = CMD_DECLARE_ENUM_SORT
    SYMBOL["define-system"] = CMD_DEFINE_SYSTEM
    SYMBOL["check-system"] = CMD_CHECK_SYSTEM

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

    # @_("LPAREN CMD_DECLARE_SORT SYMBOL NUM RPAREN")
    # def command(self, p):
    #     if not p[2] in self.sorts:
    #         self.sorts[p[2]] = int(p[3])
    #     else:
    #         print(f"Sort {p[2]} already defined.")

    #     return None
    
    # @_("LPAREN CMD_DEFINE_SORT SYMBOL _ RPAREN")
    # def command(self, p):
    #     return []
    
    # @_("LPAREN CMD_DECLARE_CONST SYMBOL SYMBOL RPAREN")
    # def command(self, p):
    #     return []
    
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

    @_("COLON ATTR_INPUT LPAREN s_expr_list RPAREN",
       "COLON ATTR_LOCAL LPAREN s_expr_list RPAREN",
       "COLON ATTR_OUTPUT LPAREN s_expr_list RPAREN")
    def define_system_attribute(self, p):
        return (str(p[1]), p[3])

    @_("COLON SYMBOL LPAREN s_expr RPAREN")
    def attribute(self, p):
        return (str(p[1]), p[3])

    @_("s_expr_list LPAREN s_expr RPAREN")
    def s_expr_list(self, p):
        p[0].append(p[2])
        return p[0]

    @_("")
    def s_expr_list(self, p):
        return []

    @_("LPAREN s_expr RPAREN")
    def s_expr(self, p):
        pass

    @_("SYMBOL")
    def s_expr(self, p):
        pass

    # Integer
    @_("INT")
    def s_expr(self, p):
        pass

    # Float
    @_("FLOAT")
    def s_expr(self, p):
        pass
    
    # Special constants
    @_("NUMERAL",
       "DECIMAL")
    def spec_constant(self, p):
        pass
