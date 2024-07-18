# type: ignore
import pathlib
import re
from typing import Optional

from src import sly
from src import log
from src import moxi

FILE_NAME = pathlib.Path(__file__).name

class Lexer(sly.Lexer):

    def __init__(self, filename: str) -> None:
        self.filename = filename

    tokens = { NUMERAL, BINARY, HEXADECIMAL, DECIMAL,
               SYMBOL, KEYWORD,
               LPAREN, RPAREN,
               RW_UNDERSCORE, RW_LET, RW_AS,
               PK_INPUT, PK_LOCAL, PK_OUTPUT, PK_INIT, PK_TRANS, PK_INV, PK_SUBSYS,
               PK_ASSUMPTION, PK_FAIRNESS, PK_REACHABLE, PK_CURRENT, PK_QUERY, PK_QUERIES,
               CMD_SET_LOGIC, CMD_DECLARE_SORT, CMD_DEFINE_SORT, CMD_DECLARE_CONST, CMD_DEFINE_FUN, CMD_DECLARE_FUN,
               CMD_DECLARE_ENUM_SORT, CMD_DEFINE_SYSTEM, CMD_CHECK_SYSTEM, CMD_EXIT }

    # String containing ignored characters between tokens
    ignore = " \t"
    ignore_comment = r";.*"
    ignore_newline = r"\n+"

    DECIMAL     = r"(0|[1-9]\d*)\.0*(0|[1-9]\d*)"
    NUMERAL     = r"0|[1-9]\d*"
    HEXADECIMAL = r"#x[A-F0-9]+"
    BINARY      = r"#b[01]+"

    SYMBOL   = r"[a-zA-Z~!@$%^&*_+=<>.?/-][0-9a-zA-Z~!@#$%^&*_+=<>.?/-]*'?|" \
               r"\|[^\\\|]*\|'?"
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
    KEYWORD[":subsys"]     = PK_SUBSYS
    KEYWORD[":assumption"] = PK_ASSUMPTION
    KEYWORD[":fairness"]   = PK_FAIRNESS
    KEYWORD[":reachable"]  = PK_REACHABLE
    KEYWORD[":current"]    = PK_CURRENT
    KEYWORD[":query"]      = PK_QUERY
    KEYWORD[":queries"]    = PK_QUERIES

    # Command names
    SYMBOL["set-logic"]  = CMD_SET_LOGIC
    SYMBOL["declare-sort"]  = CMD_DECLARE_SORT
    SYMBOL["define-sort"]   = CMD_DEFINE_SORT
    SYMBOL["declare-const"] = CMD_DECLARE_CONST
    SYMBOL["define-fun"]    = CMD_DEFINE_FUN
    SYMBOL["declare-fun"]    = CMD_DECLARE_FUN
    SYMBOL["declare-enum-sort"]  = CMD_DECLARE_ENUM_SORT
    SYMBOL["define-system"] = CMD_DEFINE_SYSTEM
    SYMBOL["check-system"]  = CMD_CHECK_SYSTEM
    SYMBOL["exit"]  = CMD_EXIT

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
        self.enums = {}

    def loc(self, token) -> log.FileLocation:
        return log.FileLocation(self.filename, token.lineno)

    def error(self, token):
        self.status = False
        log.error(f"Unexpected token ({token})", FILE_NAME, self.loc(token))

    @_("command_list command")
    def command_list(self, p):
        if p[1]:
            p[0].append(p[1])
        return p[0]

    @_("")
    def command_list(self, p):
        return []

    @_("LPAREN CMD_SET_LOGIC SYMBOL RPAREN")
    def command(self, p):
        return moxi.SetLogic(p[2], self.loc(p))

    @_("LPAREN CMD_DECLARE_SORT SYMBOL NUMERAL RPAREN")
    def command(self, p):
        return moxi.DeclareSort(p[2], p[3], self.loc(p))
    
    @_("LPAREN CMD_DEFINE_SORT labeled_symbol_list sort RPAREN")
    def command(self, p):
        label, symbol_list = p[2]
        return moxi.DefineSort(label, symbol_list, p[3], self.loc(p))
    
    @_("LPAREN CMD_DECLARE_CONST SYMBOL sort RPAREN")
    def command(self, p):
        return moxi.DeclareConst(p[2], p[3], self.loc(p))
    
    @_("LPAREN CMD_DECLARE_FUN SYMBOL LPAREN sort_list RPAREN sort RPAREN")
    def command(self, p):
        return moxi.DeclareFun(p[2], p[4], p[6], self.loc(p))
    
    @_("LPAREN CMD_DEFINE_FUN SYMBOL LPAREN sorted_var_list RPAREN sort term RPAREN")
    def command(self, p):
        return moxi.DefineFun(p[2], p[4], p[6], p[7], self.loc(p))
    
    @_("LPAREN CMD_DECLARE_ENUM_SORT labeled_symbol_list RPAREN")
    def command(self, p):
        label, symbol_list = p[2]

        values = []
        for value in symbol_list:
            values.append(value)
            self.enums[value] = label

        return moxi.DeclareEnumSort(label, values, self.loc(p))
    
    @_("LPAREN CMD_DEFINE_SYSTEM SYMBOL define_system_attribute_list RPAREN")
    def command(self, p):
        input, output, local = [], [], []
        init_expr = moxi.Constant(moxi.Sort.Bool(), True, self.loc(p))
        trans_expr = moxi.Constant(moxi.Sort.Bool(), True, self.loc(p))
        inv_expr = moxi.Constant(moxi.Sort.Bool(), True, self.loc(p))
        subsystems = {}

        if moxi.CommandAttribute.INPUT in p[3]:
            input = p[3][moxi.CommandAttribute.INPUT]
            
        if moxi.CommandAttribute.OUTPUT in p[3]:
            output = p[3][moxi.CommandAttribute.OUTPUT]

        if moxi.CommandAttribute.LOCAL in p[3]:
            local = p[3][moxi.CommandAttribute.LOCAL]
            
        if moxi.CommandAttribute.INIT in p[3]:
            init_expr = p[3][moxi.CommandAttribute.INIT]
            
        if moxi.CommandAttribute.TRANS in p[3]:
            trans_expr = p[3][moxi.CommandAttribute.TRANS]
            
        if moxi.CommandAttribute.INV in p[3]:
            inv_expr = p[3][moxi.CommandAttribute.INV]

        if moxi.CommandAttribute.SUBSYS in p[3]:
            subsystems = p[3][moxi.CommandAttribute.SUBSYS]

        return moxi.DefineSystem(str(p[2]), input, output, local, init_expr, trans_expr, inv_expr, subsystems, self.loc(p))

    @_("LPAREN CMD_CHECK_SYSTEM SYMBOL check_system_attribute_list RPAREN")
    def command(self, p):
        input, output, local, queries = [], [], [], []
        assume, fair, reach, current, query = {}, {}, {}, {}, {}

        if moxi.CommandAttribute.INPUT in p[3]:
            input = p[3][moxi.CommandAttribute.INPUT]
            
        if moxi.CommandAttribute.OUTPUT in p[3]:
            output = p[3][moxi.CommandAttribute.OUTPUT]

        if moxi.CommandAttribute.LOCAL in p[3]:
            local = p[3][moxi.CommandAttribute.LOCAL]

        if moxi.CommandAttribute.ASSUMPTION in p[3]:
            assume = p[3][moxi.CommandAttribute.ASSUMPTION]
            
        if moxi.CommandAttribute.FAIRNESS in p[3]:
            fair = p[3][moxi.CommandAttribute.FAIRNESS]
            
        if moxi.CommandAttribute.REACHABLE in p[3]:
            reach = p[3][moxi.CommandAttribute.REACHABLE]
            
        if moxi.CommandAttribute.CURRENT in p[3]:
            current = p[3][moxi.CommandAttribute.CURRENT]
            
        if moxi.CommandAttribute.QUERY in p[3]:
            query = p[3][moxi.CommandAttribute.QUERY]
            
        if moxi.CommandAttribute.QUERIES in p[3]:
            queries = p[3][moxi.CommandAttribute.QUERIES]

        return moxi.CheckSystem(p[2], input, output, local, assume, fair, reach, current, query, queries, self.loc(p))

    @_("LPAREN CMD_EXIT RPAREN")
    def command(self, p):
        return moxi.Exit()

    @_("define_system_attribute_list define_system_attribute")
    def define_system_attribute_list(self, p):
        (attr, value) = p[1]

        if attr not in p[0]:
            p[0][attr] = value
        elif attr.is_definable_once():
            log.error(f"Error:{p.lineno}: multiple instances of attribute '{attr.value}'.", FILE_NAME, self.loc(p))
            self.status = False
        elif attr.get_value_type() == dict:
            # check for duplicate symbols
            for v in value.keys():
                if v in p[0][attr]:
                    log.error(f"Error:{p.lineno}: repeat symbol for attribute {attr.value} ({v})", FILE_NAME, self.loc(p))
                    self.status = False
            p[0][attr].update(value)
        elif attr.get_value_type() == list:
            p[0][attr] += value
        elif attr.get_value_type() == moxi.Term and isinstance(attr, moxi.CommandAttribute.TRANS):
            p[0][attr] = moxi.Apply.Or([p[0][attr], value], self.loc(p))
            # p[0][attr] = moxi.Apply(moxi.Sort.NoSort(), moxi.Identifier("or", []), [p[0][attr], value], self.loc(p))
        elif attr.get_value_type() == moxi.Term and isinstance(attr, moxi.CommandAttribute.INV):
            p[0][attr] = moxi.Apply.And([p[0][attr], value], self.loc(p))
            # p[0][attr] = moxi.Apply(moxi.Sort.NoSort(), moxi.Identifier("and", []), [p[0][attr], value], self.loc(p))
        else:
            log.error(f"Error:{p.lineno}: parser error ({attr.value}).", FILE_NAME, self.loc(p))
            self.status = False

        return p[0]

    @_("")
    def define_system_attribute_list(self, p):
        return {}

    @_("PK_INPUT LPAREN sorted_var_list RPAREN")
    def define_system_attribute(self, p):
        return (moxi.CommandAttribute.INPUT, p[2])

    @_("PK_OUTPUT LPAREN sorted_var_list RPAREN")
    def define_system_attribute(self, p):
        return (moxi.CommandAttribute.OUTPUT, p[2])

    @_("PK_LOCAL LPAREN sorted_var_list RPAREN")
    def define_system_attribute(self, p):
        return (moxi.CommandAttribute.LOCAL, p[2])

    @_("PK_INIT term")
    def define_system_attribute(self, p):
        return (moxi.CommandAttribute.INIT, p[1])

    @_("PK_TRANS term")
    def define_system_attribute(self, p):
        return (moxi.CommandAttribute.TRANS, p[1])

    @_("PK_INV term")
    def define_system_attribute(self, p):
        return (moxi.CommandAttribute.INV, p[1])

    @_("PK_SUBSYS LPAREN SYMBOL LPAREN SYMBOL symbol_list RPAREN RPAREN")
    def define_system_attribute(self, p):
        return (moxi.CommandAttribute.SUBSYS, {p[2] : (p[4], p[5])})

    @_("check_system_attribute_list check_system_attribute")
    def check_system_attribute_list(self, p):
        (attr, value) = p[1]

        if attr not in p[0]:
            p[0][attr] = value
        elif attr.is_definable_once():
            log.error(f"Error:{p.lineno}: multiple instances of attribute '{attr.value}'.", FILE_NAME, self.loc(p))
            self.status = False
        elif attr.get_value_type() == dict:
            # check for duplicate symbols
            if [v for v in value.keys() if v in p[0][attr]]:
                log.error(f"Error:{p.lineno}: repeat symbol for attribute '{attr.value}'.", FILE_NAME, self.loc(p))
                self.status = False
            p[0][attr].update(value)
        elif attr.get_value_type() == list:
            p[0][attr] += value
        else:
            log.error(f"Error:{p.lineno}: parser error ({attr.value}).", FILE_NAME, self.loc(p))
            self.status = False

        return p[0]

    @_("")
    def check_system_attribute_list(self, p):
        return {}

    @_("PK_INPUT LPAREN sorted_var_list RPAREN")
    def check_system_attribute(self, p):
        return (moxi.CommandAttribute.INPUT, p[2])

    @_("PK_OUTPUT LPAREN sorted_var_list RPAREN")
    def check_system_attribute(self, p):
        return (moxi.CommandAttribute.OUTPUT, p[2])

    @_("PK_LOCAL LPAREN sorted_var_list RPAREN")
    def check_system_attribute(self, p):
        return (moxi.CommandAttribute.LOCAL, p[2])

    @_("PK_ASSUMPTION LPAREN SYMBOL term RPAREN")
    def check_system_attribute(self, p):
        return (moxi.CommandAttribute.ASSUMPTION, {p[2]: p[3]})

    @_("PK_FAIRNESS LPAREN SYMBOL term RPAREN")
    def check_system_attribute(self, p):
        return (moxi.CommandAttribute.FAIRNESS, {p[2]: p[3]})

    @_("PK_REACHABLE LPAREN SYMBOL term RPAREN")
    def check_system_attribute(self, p):
        return (moxi.CommandAttribute.REACHABLE, {p[2]: p[3]})

    @_("PK_CURRENT LPAREN SYMBOL term RPAREN")
    def check_system_attribute(self, p):
        return (moxi.CommandAttribute.CURRENT, {p[2]: p[3]})

    @_("PK_QUERY LPAREN labeled_symbol_list RPAREN")
    def check_system_attribute(self, p):
        label,symbol_list = p[2]
        return (moxi.CommandAttribute.QUERY, {label: symbol_list})

    @_("PK_QUERIES LPAREN labeled_symbol_list_list RPAREN")
    def check_system_attribute(self, p):
        return (moxi.CommandAttribute.QUERIES, [p[2]])
    
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
        elif symbol in self.enums:
            return moxi.Constant.Enum(self.enums[symbol], symbol)

        prime: bool = False
        if symbol[len(symbol)-1] == "'":
            prime = True
            symbol = symbol[:-1]

        return moxi.Variable(moxi.Sort.NoSort(), symbol, prime, self.loc(p))

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


def parse(input_path: pathlib.Path) -> Optional[moxi.Program]:
    """Parse contents of `input_path` and returns corresponding program on success, else returns None."""
    with open(str(input_path), "r") as f:
        content = f.read()

    lexer: Lexer = Lexer(input_path.name)
    parser: Parser = Parser(input_path.name)

    cmds = parser.parse(lexer.tokenize(content))

    if parser.status and cmds:
        return moxi.Program(cmds)
    
    return None

