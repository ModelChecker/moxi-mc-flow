# type: ignore
import pathlib
from typing import Optional
import re

from src import sly, log, vmt, moxi

FILE_NAME = pathlib.Path(__file__).name

class Lexer(sly.Lexer):

    def __init__(self, filename: str) -> None:
        self.filename = filename

    tokens = { NUMERAL, BINARY, HEXADECIMAL, DECIMAL,
               SYMBOL, KEYWORD,
               LPAREN, RPAREN,
               RW_UNDERSCORE, RW_LET, RW_AS, RW_BANG,
               PK_INIT, PK_NEXT, PK_INVAR_PROPERTY, PK_LIVE_PROPERTY, PK_TRANS, PK_PREDICATE,
               CMD_SET_LOGIC, CMD_SET_INFO, CMD_DECLARE_SORT, CMD_DEFINE_SORT, 
               CMD_DECLARE_CONST, CMD_DEFINE_FUN, CMD_DECLARE_FUN, CMD_ASSERT }

    # String containing ignored characters between tokens
    ignore = " \t"
    ignore_comment = r";.*"
    ignore_newline = r"\n+"

    DECIMAL     = r"(0|[1-9]\d*)\.0*(0|[1-9]\d*)"
    NUMERAL     = r"0|[1-9]\d*"
    HEXADECIMAL = r"#x[A-F0-9]+"
    BINARY      = r"#b[01]+"

    SYMBOL   = r"[a-zA-Z~!@$%^&*_+=<>.?/-][0-9a-zA-Z~!@#$%^&*_+=<>.?/-]*'?|" \
               r"\|[^\\\|]*\|"
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
    SYMBOL["!"]           = RW_BANG
    SYMBOL["as"]          = RW_AS
    # SYMBOL["exists"]      = RW_EXISTS
    # SYMBOL["forall"]      = RW_FORALL
    # SYMBOL["match"]       = RW_MATCH
    # SYMBOL["par"]         = RW_PAR

    # Predefined keywords
    KEYWORD[":init"]  = PK_INIT
    KEYWORD[":next"]  = PK_NEXT
    KEYWORD[":trans"] = PK_TRANS
    KEYWORD[":predicate"] = PK_PREDICATE
    # KEYWORD[":invar"] = PK_INVAR
    KEYWORD[":invar-property"] = PK_INVAR_PROPERTY
    KEYWORD[":live-property"] = PK_LIVE_PROPERTY

    # Command names
    SYMBOL["set-info"]      = CMD_SET_INFO
    SYMBOL["set-logic"]     = CMD_SET_LOGIC
    SYMBOL["declare-sort"]  = CMD_DECLARE_SORT
    SYMBOL["define-sort"]   = CMD_DEFINE_SORT
    SYMBOL["declare-const"] = CMD_DECLARE_CONST
    SYMBOL["define-fun"]    = CMD_DEFINE_FUN
    SYMBOL["declare-fun"]   = CMD_DECLARE_FUN
    SYMBOL["assert"]        = CMD_ASSERT

    # Extra action for newlines
    def ignore_newline(self, t):
        self.lineno += t.value.count("\n")

    def error(self, t):
        loc = log.FileLocation(self.filename, self.lineno)
        log.error(f"{self.lineno}: Illegal character \"%s\" {t.value[0]}", FILE_NAME, loc)
        self.index += 1


class Parser(sly.Parser):
    tokens = Lexer.tokens

    def __init__(self, filename: str) :
        super().__init__()
        self.filename = filename
        self.status = True
        self.vars = []
        self.source = {} # back-mapping of next vars to cur vars
        self.next = {}
        self.trans = []
        self.init = []
        self.invar_props = {}
        self.live_props = {}
        self.funs = {}

    def loc(self, token) -> log.FileLocation:
        return log.FileLocation(self.filename, token.lineno)

    def error(self, token):
        self.status = False
        log.error(f"Unexpected token ({token})", FILE_NAME, self.loc(token))

    @_("command_list command")
    def command_list(self, p):
        pass

    @_("")
    def command_list(self, p):
        pass

    @_("LPAREN CMD_SET_LOGIC SYMBOL RPAREN")
    def command(self, p):
        pass

    @_("LPAREN CMD_SET_INFO KEYWORD symbol_list RPAREN")
    def command(self, p):
        pass

    @_("LPAREN CMD_DECLARE_SORT SYMBOL NUMERAL RPAREN")
    def command(self, p):
        pass
    
    @_("LPAREN CMD_DEFINE_SORT labeled_symbol_list sort RPAREN")
    def command(self, p):
        pass
    
    @_("LPAREN CMD_DECLARE_CONST SYMBOL sort RPAREN")
    def command(self, p):
        self.vars.add((p[2], p[3]))
    
    @_("LPAREN CMD_DECLARE_FUN SYMBOL LPAREN sorted_var_list RPAREN sort RPAREN")
    def command(self, p):
        if len(p[4]) == 0:
            self.vars.append((p[2], p[6]))
    
    @_("LPAREN CMD_DEFINE_FUN SYMBOL LPAREN sorted_var_list RPAREN sort term RPAREN")
    def command(self, p):
        if ":next" in p[7].attrs:
            self.source[p[7].attrs[":next"]] = (p[7].str_no_attrs(), p[6])
            self.next[p[7].str_no_attrs()] = (p[7].attrs[":next"], p[6])
        if ":init" in p[7].attrs:
            self.init.append(p[7])
        if ":trans" in p[7].attrs:
            self.trans.append(p[7])
        if ":invar-property" in p[7].attrs:
            self.invar_props[p[7].attrs[":invar-property"]] = p[7]
        if ":live-property" in p[7].attrs:
            self.live_props[p[7].attrs[":live-property"]] = p[7]

        self.funs[p[2]] = (p[6], p[7])
    
    @_("LPAREN CMD_ASSERT SYMBOL RPAREN")
    def command(self, p):
        if p[2] != "true":
            log.error("Only '(assert true)' allowed for assertions", FILE_NAME, self.loc(p))
            self.status = False
    
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

    @_("labeled_symbol_list_list LPAREN labeled_symbol_list RPAREN")
    def labeled_symbol_list_list(self, p):
        label, symbol_list = p[2]
        if label in p[0]:
            log.error(f"Error:{p.lineno}: repeat label in queries attribute '{label}'.", FILE_NAME, self.loc(p))
            self.status = False
        p[0][label] = symbol_list
        return p[0]

    @_("")
    def labeled_symbol_list_list(self, p):
        return {}

    @_("SYMBOL LPAREN symbol_list RPAREN")
    def labeled_symbol_list(self, p):
        return (p[0], p[2])

    @_("")
    def labeled_symbol_list(self, p):
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
        if re.match(r"bv\d+", p[0].symbol):
            if len(p[0].indices) != 1:
                log.error(f"Error, bit vector constants must have one index ({p[0]}).", FILE_NAME, self.loc(p))
                self.status = False
                return moxi.Constant(moxi.Sort.BitVec(0), 0)

            width = int(p[0].indices[0]) 
            return moxi.Constant(moxi.Sort.BitVec(width), int(p[0].symbol[2:]))

        if len(p[0].indices) > 0:
            log.error(f"Error, simple term identifiers cannot be indexed ({p[0]}).", FILE_NAME, self.loc(p))
            self.status = False

        symbol: str = p[0].symbol
        if symbol == "true":
            return moxi.Constant.Bool(True)
        elif symbol == "false":
            return moxi.Constant.Bool(False)

        return moxi.Variable(moxi.Sort.NoSort(), symbol, False, self.loc(p))

    @_("NUMERAL")
    def term(self, p):
        return moxi.Constant.Int(int(p[0]))

    @_("DECIMAL")
    def term(self, p):
        return moxi.Constant.Real(float(p[0]))

    @_("HEXADECIMAL") # example: "#x123"
    def term(self, p):
        return moxi.Constant.BitVec(len(p[0][2:])*4, int(p[0][2:], base=16))

    @_("BINARY") # example: "#b101"
    def term(self, p):
        return moxi.Constant.BitVec(len(p[0][2:]), int(p[0][2:], base=2))

    @_("LPAREN identifier term_list term RPAREN")
    def term(self, p):
        p[2].append(p[3])
        return moxi.Apply(moxi.Sort.NoSort(), p[1], p[2], self.loc(p))

    @_("LPAREN RW_LET LPAREN bound_var_list RPAREN term RPAREN")
    def term(self, p):
        return moxi.LetTerm(moxi.Sort.NoSort(), p[3], p[5], self.loc(p))

    @_("LPAREN qualified_identifier term RPAREN")
    def term(self, p):
        ident, sort = p[1]
        return moxi.Apply(sort, ident, [p[2]], self.loc(p))

    @_("LPAREN term RPAREN")
    def term(self, p):
        return p[1]

    @_("LPAREN RW_BANG term attribute_list attribute RPAREN")
    def term(self, p):
        p[3].append(p[4])
        for keyword,value in p[3]:
            p[2].add_attribute(keyword, value)
        return p[2]

    @_("PK_INIT SYMBOL",
       "PK_TRANS SYMBOL",
       "PK_PREDICATE SYMBOL")
    def attribute(self, p):
        if p[1] != "true":
            log.error(f"Annotation '{p[0]}' must have value 'true'", FILE_NAME, self.loc(p))
            self.status = False
        return (p[0], p[1])

    @_("PK_NEXT SYMBOL")
    def attribute(self, p):
        return (p[0], p[1])

    @_("PK_INVAR_PROPERTY NUMERAL",
       "PK_LIVE_PROPERTY NUMERAL")
    def attribute(self, p):
        return (p[0], p[1])
    
    @_("KEYWORD SYMBOL")
    def attribute(self, p):
        log.error(f"Keyword '{p[0]}' not recognized", FILE_NAME, self.loc(p))
        self.status = False
        return (p[0], p[1])

    @_("KEYWORD NUMERAL")
    def attribute(self, p):
        return (p[0], p[1])
    
    @_("attribute_list attribute")
    def attribute_list(self, p):
        p[0].append(p[1])
        return p[0]

    @_("")
    def attribute_list(self, p):
        return []

    @_("identifier")
    def sort(self, p):
        return moxi.Sort(p[0], [])

    @_("LPAREN identifier sort_list sort RPAREN")
    def sort(self, p):
        p[2].append(p[3])
        return moxi.Sort(p[1], p[2])

    @_("sort_list sort")
    def sort_list(self, p):
        p[0].append(p[1])
        return p[0]

    @_("")
    def sort_list(self, p):
        return []

    @_("LPAREN RW_AS identifier sort RPAREN")
    def qualified_identifier(self, p):
        return (p[2], p[3])

    # Identifiers
    @_("SYMBOL")
    def identifier(self, p):
        return moxi.Identifier(p[0], [])

    @_("LPAREN RW_UNDERSCORE SYMBOL index_list index RPAREN")
    def identifier(self, p):
        p[3].append(p[4])
        return moxi.Identifier(p[2], p[3])

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


def parse(input_path: pathlib.Path) -> Optional[vmt.Program]:
    """Parse contents of `input_path` and returns corresponding program on success, else returns None."""
    with open(str(input_path), "r") as f:
        content = f.read()

    lexer: Lexer = Lexer(input_path.name)
    parser: Parser = Parser(input_path.name)

    parser.parse(lexer.tokenize(content))

    if parser.status:
        return vmt.Program(
            parser.vars, 
            parser.source, 
            parser.next,
            parser.init, 
            parser.trans, 
            parser.invar_props, 
            parser.live_props,
            parser.funs
        )
    
    return None

