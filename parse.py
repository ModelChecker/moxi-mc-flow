#type: ignore
from typing import ItemsView
from sly import Lexer, Parser
from mochil import *

class MCILLexer(Lexer):

    tokens = { NUMERAL, BINARY,
               SYMBOL, KEYWORD,
               LPAREN, RPAREN,
               RW_UNDERSCORE,
               PK_INPUT, PK_LOCAL, PK_OUTPUT, PK_INIT, PK_TRANS, PK_INV, PK_SUBSYS,
               PK_ASSUMPTION, PK_FAIRNESS, PK_REACHABLE, PK_CURRENT, PK_QUERY,
               CMD_DECLARE_SORT, CMD_DEFINE_SORT, CMD_DECLARE_CONST, CMD_DEFINE_FUN, 
               CMD_DEFINE_SYSTEM, CMD_CHECK_SYSTEM, CMD_EXIT }

    # String containing ignored characters between tokens
    ignore = " \t"
    ignore_comment = r";.*"
    ignore_newline = r"\n+"

    NUMERAL     = r"0|[1-9]\d*"
    # DECIMAL     = r"-?\d*\.\d+"
    # HEXADECIMAL = r"#x[A-F0-9]+"
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
    #SYMBOL["declare-enum"]  = CMD_DECLARE_ENUM_SORT
    SYMBOL["define-system"] = CMD_DEFINE_SYSTEM
    SYMBOL["check-system"]  = CMD_CHECK_SYSTEM
    SYMBOL["exit"]  = CMD_EXIT

    # Extra action for newlines
    def ignore_newline(self, t):
        self.lineno += t.value.count("\n")

    def error(self, t):
        print(f"{self.lineno}: Illegal character \"%s\" {t.value[0]}")
        self.index += 1


class MCILParser(Parser):
    tokens = MCILLexer.tokens

    def __init__(self) -> None:
        super().__init__()
        self.input_context = []
        self.output_context = []
        self.local_context = []
        self.logic_context = []
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
        return MPTDeclareSort(p[2], p[3])
    
    @_("LPAREN CMD_DEFINE_SORT SYMBOL LPAREN sort_list RPAREN RPAREN")
    def command(self, p):
        return None
    
    @_("LPAREN CMD_DECLARE_CONST SYMBOL sort RPAREN")
    def command(self, p):
        self.logic_context.append((p[2], p[3]))
        return MPTDeclareConst(p[2], p[3])
    
    @_("LPAREN CMD_DEFINE_FUN SYMBOL LPAREN sort_list RPAREN RPAREN")
    def command(self, p):
        return None
    
    # @_("LPAREN CMD_DECLARE_ENUM_SORT SYMBOL LPAREN symbol_list RPAREN RPAREN")
    # def command(self, p):
    #     return []
    
    @_("LPAREN CMD_DEFINE_SYSTEM SYMBOL define_system_attribute_list RPAREN")
    def command(self, p):
        if MPTAttribute.INPUT.value in p[3]:
            in_vars = p[3][MPTAttribute.INPUT.value]
            self.input_context = []
        else:
            in_vars = {}
            
        if MPTAttribute.OUTPUT.value in p[3]:
            out_vars = p[3][MPTAttribute.OUTPUT.value]
            self.output_context = []
        else:
            out_vars = {}

        if MPTAttribute.LOCAL.value in p[3]:
            local_vars = p[3][MPTAttribute.LOCAL.value]
            self.local_context = []
        else:
            local_vars = {}
            
        if MPTAttribute.INIT.value in p[3]:
            init_expr = p[3][MPTAttribute.INIT.value]
        else:
            init_expr = MPTConstant(MPT_BOOL_SORT, True)
            
        if MPTAttribute.TRANS.value in p[3]:
            trans_expr = p[3][MPTAttribute.TRANS.value]
        else:
            trans_expr = MPTConstant(MPT_BOOL_SORT, True)
            
        if MPTAttribute.INV.value in p[3]:
            inv_expr = p[3][MPTAttribute.TRANS.value]
        else:
            inv_expr = MPTConstant(MPT_BOOL_SORT, True)

        return MPTDefineSystem(str(p[2]), in_vars, out_vars, local_vars,
            init_expr, trans_expr, inv_expr, [])

    @_("LPAREN CMD_CHECK_SYSTEM SYMBOL check_system_attribute_list RPAREN")
    def command(self, p):
        if MPTAttribute.INPUT.value in p[3]:
            in_vars = p[3][MPTAttribute.INPUT.value]
            self.input_context = []
        else:
            in_vars = {}
            
        if MPTAttribute.OUTPUT.value in p[3]:
            out_vars = p[3][MPTAttribute.OUTPUT.value]
            self.output_context = []
        else:
            out_vars = {}

        if MPTAttribute.LOCAL.value in p[3]:
            local_vars = p[3][MPTAttribute.LOCAL.value]
            self.local_context = []
        else:
            local_vars = {}
            
        if MPTAttribute.ASSUMPTION.value in p[3]:
            assume_dict = p[3][MPTAttribute.ASSUMPTION.value]
        else:
            assume_dict = {}
            
        if MPTAttribute.FAIRNESS.value in p[3]:
            fair_dict = p[3][MPTAttribute.FAIRNESS.value]
        else:
            fair_dict = {}
            
        if MPTAttribute.REACHABLE.value in p[3]:
            reach_dict = p[3][MPTAttribute.REACHABLE.value]
        else:
            reach_dict = {}
            
        if MPTAttribute.CURRENT.value in p[3]:
            current_dict = p[3][MPTAttribute.CURRENT.value]
        else:
            current_dict = {}
            
        if MPTAttribute.QUERY.value in p[3]:
            query_dict = p[3][MPTAttribute.QUERY.value]
        else:
            query_dict = {}

        return MPTCheckSystem(p[2], in_vars, out_vars, local_vars,
            assume_dict, fair_dict, reach_dict, current_dict, query_dict)

    @_("LPAREN CMD_EXIT RPAREN")
    def command(self, p):
        return MPTExit()

    @_("define_system_attribute_list define_system_attribute")
    def define_system_attribute_list(self, p):
        if p[1][0] in p[0]:
            print(f"Error: multiple instances of attribute ({p[1][0]}).")
            self.status = False
        p[0][p[1][0]] = p[1][1]
        return p[0]

    @_("")
    def define_system_attribute_list(self, p):
        return {}

    @_("PK_INPUT LPAREN sorted_var_list RPAREN")
    def define_system_attribute(self, p):
        self.input_context = p[2]
        return (p[0], p[2])

    @_("PK_OUTPUT LPAREN sorted_var_list RPAREN")
    def define_system_attribute(self, p):
        self.output_context = p[2]
        return (p[0], p[2])

    @_("PK_LOCAL LPAREN sorted_var_list RPAREN")
    def define_system_attribute(self, p):
        self.local_context = p[2]
        return (p[0], p[2])

    @_("PK_INIT term",
       "PK_TRANS term",
       "PK_INV term")
    def define_system_attribute(self, p):
        return (p[0], p[1])

    @_("PK_SUBSYS LPAREN SYMBOL LPAREN SYMBOL symbol_list symbol_list RPAREN RPAREN")
    def define_system_attribute(self, p):
        return (p[0], (p[2], p[4], p[5], p[6]))

    @_("check_system_attribute_list check_system_attribute")
    def check_system_attribute_list(self, p):
        if p[1][0] == MPTAttribute.INPUT.value or p[1][0] == MPTAttribute.OUTPUT.value or p[1][0] == MPTAttribute.LOCAL.value:
            if p[1][0] in p[0]:
                print(f"Error: multiple instances of attribute ({p[1][0]}).")
                self.status = False
            p[0][p[1][0]] = p[1][1]
            return p[0]
        else:
            if not p[1][0] in p[0]:
                p[0][p[1][0]] = {}
            p[0][p[1][0]].update(p[1][1])
            return p[0]

    @_("")
    def check_system_attribute_list(self, p):
        return {}

    @_("PK_INPUT LPAREN sorted_var_list RPAREN")
    def check_system_attribute(self, p):
        self.input_context = p[2]
        return (p[0], p[2])

    @_("PK_OUTPUT LPAREN sorted_var_list RPAREN")
    def check_system_attribute(self, p):
        self.output_context = p[2]
        return (p[0], p[2])

    @_("PK_LOCAL LPAREN sorted_var_list RPAREN")
    def check_system_attribute(self, p):
        self.local_context = p[2]
        return (p[0], p[2])

    @_("PK_ASSUMPTION LPAREN SYMBOL term RPAREN",
       "PK_FAIRNESS LPAREN SYMBOL term RPAREN",
       "PK_REACHABLE LPAREN SYMBOL term RPAREN",
       "PK_CURRENT LPAREN SYMBOL term RPAREN")
    def check_system_attribute(self, p):
        return (p[0], {p[2]: p[3]})

    @_("PK_QUERY LPAREN SYMBOL LPAREN symbol_list SYMBOL RPAREN RPAREN")
    def check_system_attribute(self, p):
        p[4].append(p[5])
        return (p[0], {p[2]: p[4]})
    
    @_("sorted_var_list LPAREN sorted_var RPAREN")
    def sorted_var_list(self, p):
        p[0].append(p[2])
        return p[0]
    
    @_("")
    def sorted_var_list(self, p):
        return []
    
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
            print("Error, variable identifiers must not be indexed.")
            self.status = False

        symbol: str = p[0].symbol
        prime: bool = False
        if symbol[len(symbol)-1] == "'":
            prime = True
            symbol = symbol[:-1]

        for sym,sort in self.input_context:
            if sym == symbol:
                return MPTInputVar(sort, symbol, prime)

        for sym,sort in self.output_context:
            if sym == symbol:
                return MPTOutputVar(sort, symbol, prime)

        for sym,sort in self.local_context:
            if sym == symbol:
                return MPTLocalVar(sort, symbol, prime)

        for sym,sort in self.logic_context:
            if prime:
                print(f"Error: logic variable cannot be primed ({symbol}).")
                self.status = False
            if symbol == sym:
                return MPTLogicVar(sort, symbol)

        print(f"Error: variable undeclared ({symbol})")
        self.status = False

    @_("NUMERAL")
    def term(self, p):
        return MPTConstant(MPT_NO_SORT, int(p[0]))

    @_("BINARY")
    def term(self, p):
        return MPTConstant(MPT_BITVEC_SORT(len(p[0][2:])), int(p[0][2:], base=2))

    @_("LPAREN identifier term_list term RPAREN")
    def term(self, p):
        p[2].append(p[3])
        return MPTApply(MPT_NO_SORT, p[1], p[2])

    @_("identifier")
    def sort(self, p):
        return MPTSort(p[0], [])

    @_("LPAREN identifier sort_list sort RPAREN")
    def sort(self, p):
        p[2].append(p[3])
        return MPTSort(p[0], p[2])

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
        return MPTIdentifier(p[0], [])

    @_("LPAREN RW_UNDERSCORE SYMBOL index_list index RPAREN")
    def identifier(self, p):
        p[3].append(p[4])
        return MPTIdentifier(p[2], p[3])

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

