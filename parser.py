#type: ignore

from .sly import Lexer, Parser


str_declare_sort = "declare-sort"
str_define_sort = "define-sort"
str_declare_const = "declare-const"
str_define_fun = "define-fun"
str_declare_enum_sort = "declare-enum-sort"
str_define_system = "define-system"
str_check_system = "check-system"


class ILLexer(Lexer):

    tokens = { KW_DECLARE_SORT, KW_DEFINE_SORT, KW_DECLARE_CONST, KW_DEFINE_FUN, 
               KW_DECLARE_ENUM_SORT, KW_DEFINE_SYSTEM, KW_CHECK_SYSTEM,
               LOG_NEG, LOG_AND, LOG_OR, LOG_IMPL, LOG_IFF, #LOG_XOR,
               REL_EQ, REL_NEQ, REL_GTE, REL_LTE, REL_GT, REL_LT,
               ARITH_ADD, ARITH_SUB, ARITH_MUL, ARITH_DIV, ARITH_MOD, #ARITH_POW, ARITH_SQRT, ARITH_PM,
               ASSIGN, SYMBOL, NUM, FLOAT, INT, SEMI, COLON, DOT, COMMA, QUEST,
               LBRACK, RBRACK, LBRACE, RBRACE, LPAREN, RPAREN }

    # String containing ignored characters between tokens
    ignore = " \t"
    ignore_comment = r"--.*"
    ignore_newline = r"\n+"

    REL_NEQ = r"!=|≠" # longer tokens must come first
    NUM     = r"0|[1-9]\d*"
    FLOAT   = r"-?\d*\.\d+"
    INT     = r"-?[1-9][0-9]*|0"

    # Propositional logic ops/literals
    LOG_NEG  = r"!|¬"
    LOG_AND  = r"&&|∧"
    LOG_OR   = r"\|\||∨"
    # LOG_XOR  = r"XOR|⊕"
    LOG_IMPL = r"->|→"
    LOG_IFF  = r"<->|↔"

    # Bitwise ops
    BW_NEG          = r"~"
    BW_AND          = r"&" 
    BW_OR           = r"\|" 
    BW_XOR          = r"\^" 
    BW_SHIFT_LEFT   = r"<<"
    BW_SHIFT_RIGHT  = r">>"

    # Relational ops
    REL_EQ  = r"=="
    REL_GTE = r">=|≥"
    REL_LTE = r"<=|≤" 
    REL_GT  = r">"
    REL_LT  = r"<"

    # Arithmetic ops
    ARITH_ADD   = r"\+"
    ARITH_SUB   = r"-"
    ARITH_MUL   = r"\*|•|⋅"
    ARITH_DIV   = r"/|÷"
    ARITH_MOD   = r"%"

    # Others
    ASSIGN  = r"="
    SYMBOL  = r"[a-zA-Z_][a-zA-Z0-9_]*"
    # QUEST   = r"\?"
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

    SYMBOL[str_declare_sort] = KW_DECLARE_SORT
    SYMBOL[str_define_sort] = KW_DEFINE_SORT
    SYMBOL[str_declare_const] = KW_DECLARE_CONST
    SYMBOL[str_define_fun] = KW_DEFINE_FUN
    SYMBOL[str_declare_enum_sort] = KW_DECLARE_ENUM_SORT
    SYMBOL[str_define_system] = KW_DEFINE_SYSTEM
    SYMBOL[str_check_system] = KW_CHECK_SYSTEM

    # Extra action for newlines
    def ignore_newline(self, t):
        self.lineno += t.value.count("\n")

    def error(self, t):
        # logger.error(f"{self.lineno}: Illegal character \"%s\" {t.value[0]}")
        self.index += 1


class ILParser(Parser):
    tokens = ILLexer.tokens

    precedence = (
        ("left", LOG_IMPL, LOG_IFF),
        ("left", LOG_OR),
        ("left", LOG_AND),
        ("left", REL_EQ, REL_NEQ),
        ("left", REL_GT, REL_LT, REL_GTE, REL_LTE),
        ("left", ARITH_ADD, ARITH_SUB),
        ("left", ARITH_MUL, ARITH_DIV, ARITH_MOD),
        ("right", LOG_NEG, UNARY_ARITH_SUB),
        ("right", LPAREN, DOT)
    )

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

    @_("LPAREN KW_DECLARE_SORT SYMBOL NUM RPAREN")
    def command(self, p):
        if not p[2] in self.sorts:
            self.sorts[p[2]] = int(p[3])
        else:
            print(f"Sort {p[2]} already defined.")

        return None
    
    # @_("LPAREN KW_DEFINE_SORT SYMBOL _ RPAREN")
    # def command(self, p):
    #     return []
    
    # @_("LPAREN KW_DECLARE_CONST SYMBOL SYMBOL RPAREN")
    # def command(self, p):
    #     return []
    
    # @_("LPAREN KW_DEFINE_FUN SYMBOL _ RPAREN")
    # def command(self, p):
    #     return []
    
    # @_("LPAREN KW_DECLARE_ENUM_SORT SYMBOL LPAREN symbol_list RPAREN RPAREN")
    # def command(self, p):
    #     return []
    
    @_("LPAREN KW_DEFINE_SYSTEM attribute_list RPAREN")
    def command(self, p):
        return []

    @_("attribute_list attribute")
    def attribute_list(self, p):
        return []

    @_("")
    def attribute_list(self, p):
        return []

    @_("COLON SYMBOL ")
    def attribute(self, p):
        return []

    



    @_("expr_list COMMA expr")
    def expr_list(self, p):
        p[0].append(p[2])
        return p[0]

    @_("")
    def expr_list(self, p):
        return []

    # Set expression
    @_("LBRACE expr expr_list RBRACE")
    def expr(self, p):
        return Set(p.lineno, [p[1]]+p[2])

    # Empty set expression
    @_("LBRACE RBRACE")
    def expr(self, p):
        return Set(ln, [])

    # Set aggregation expression with parameter
    @_("SYMBOL LPAREN SYMBOL bind_rule COLON expr COMMA expr RPAREN LPAREN expr RPAREN")
    def expr(self, p):
        ln = p.lineno
        operator = p[0]
        variable_name = p[2]
        mset = p[5]
        param = p[7]
        expr = p[10]

        boundvar = Variable(ln, variable_name)
        del self.defs[variable_name]

        if operator == "forexactlyn":
            return ForExactlyN(ln, mset, param, boundvar, expr)
        elif operator == "foratleastn":
            return ForAtLeastN(ln, mset, param, boundvar, expr)
        elif operator == "foratmostn":
            return ForAtMostN(ln, mset, param, boundvar, expr)
        else:
            self.error(f"{ln}: Set aggregation operator \"{operator}\" not supported")
            self.status = False
            return Node(ln, [])

    # Set aggregation expression
    @_("SYMBOL LPAREN SYMBOL bind_rule COLON expr RPAREN LPAREN expr RPAREN")
    def expr(self, p):
        ln = p.lineno
        operator = p[0]
        variable_name = p[2]
        mset = p[5]
        expr = p[8]

        boundvar = Variable(ln, variable_name)
        del self.defs[variable_name]

        if operator == "foreach":
            return ForEach(ln, mset, boundvar, expr)
        elif operator == "forsome":
            return ForSome(ln, mset, boundvar, expr)
        else:
            self.error(f"{ln}: Set aggregation operator \"{operator}\" not supported")
            self.status = False
            return Node(ln, [])

    # Stub rule for binding a set agg variable
    @_("")
    def bind_rule(self, p):
        variable_name = p[-1]
        self.defs[variable_name] = Variable(0, variable_name)

        # TODO: p is empty, so p.lineno does not work
        # how to get boundvar the correct lineno?

    # Function/struct constructor expression nonempty arguments
    @_("SYMBOL LPAREN expr expr_list RPAREN")
    def expr(self, p):
        ln = p.lineno
        expr_list = [p[2]]+p[3]
        symbol = p[0]

        if symbol in self.structs.keys():
            members: dict[str,Node] = {}
            if len(expr_list) == len(self.structs[symbol]):
                for s in self.structs[symbol].keys():
                    members[s] = expr_list.pop(0)
                return Struct(ln, symbol, members)
            else:
                logger.error(f"{ln}: Member mismatch for struct \"{symbol}\", number of members do not match")
                self.status = False
                return Node(ln, [])
        else:
            return Function(ln, symbol, expr_list)

    # Function/struct constructor expression empty arguments
    @_("SYMBOL LPAREN RPAREN")
    def expr(self, p):
        ln = p.lineno
        symbol = p[0]

        if symbol in self.structs.keys():
            if len(self.structs[symbol]) == 0:
                return Struct(ln,symbol,[])
            else:
                logger.error(f"{ln}: Member mismatch for struct \"{symbol}\", number of members do not match")
                self.status = False
                return Node(ln, [])
        else:
            logger.error(f"{ln}: Symbol \"{symbol}\" not recognized")
            self.status = False
            return Node(ln, [])

    # Struct member access
    @_("expr DOT SYMBOL")
    def expr(self, p):
        return StructAccess(p.lineno, p[0], p[2])

    # Unary expressions
    @_("LOG_NEG expr",
       "BW_NEG expr",
       "ARITH_SUB expr %prec UNARY_ARITH_SUB")
    def expr(self, p):
        ln = p.lineno
        operator = p[0]

        if operator == "!":
            return LogicalNegate(ln, p[1])
        elif operator == "~":
            return BitwiseNegate(ln, p[1])
        elif operator == "-":
            return ArithmeticNegate(ln, p[1])
        else:
            logger.error(f"{ln}: Bad expression")
            self.status = False
            return Node(ln, [])

    # Binary expressions
    @_("expr LOG_IMPL expr",
       "expr LOG_IFF expr",
       "expr LOG_OR expr",
       "expr LOG_AND expr",
       "expr BW_OR expr",
       "expr BW_XOR expr",
       "expr BW_AND expr",
       "expr REL_EQ expr",
       "expr REL_NEQ expr",
       "expr REL_GT expr",
       "expr REL_LT expr",
       "expr REL_GTE expr",
       "expr REL_LTE expr",
       "expr BW_SHIFT_LEFT expr",
       "expr BW_SHIFT_RIGHT expr",
       "expr ARITH_ADD expr",
       "expr ARITH_SUB expr",
       "expr ARITH_MUL expr",
       "expr ARITH_DIV expr",
       "expr ARITH_MOD expr")
    def expr(self, p):
        ln = p.lineno
        operator = p[1]
        lhs = p[0]
        rhs = p[2]

        if operator == "->":
            return LogicalImplies(ln, lhs, rhs)
        elif operator == "<->":
            return LogicalIff(ln, lhs, rhs)
        elif operator == "||":
            return LogicalOr(ln, [lhs, rhs])
        elif operator == "&&":
            return LogicalAnd(ln, [lhs, rhs])
        elif operator == "|":
            return BitwiseOr(ln, lhs, rhs)
        elif operator == "^":
            return BitwiseXor(ln, lhs, rhs)
        elif operator == "&":
            return BitwiseAnd(ln, lhs, rhs)
        elif operator == "==":
            return Equal(ln, lhs, rhs)
        elif operator == "!=":
            return NotEqual(ln, lhs, rhs)
        elif operator == ">":
            return GreaterThan(ln, lhs, rhs)
        elif operator == "<":
            return LessThan(ln, lhs, rhs)
        elif operator == ">=":
            return GreaterThanOrEqual(ln, lhs, rhs)
        elif operator == "<=":
            return LessThanOrEqual(ln, lhs, rhs)
        elif operator == "<<":
            return BitwiseShiftLeft(ln, lhs, rhs)
        elif operator == ">>":
            return BitwiseShiftRight(ln, lhs, rhs)
        elif operator == "+":
            return ArithmeticAdd(ln, lhs, rhs)
        elif operator == "-":
            return ArithmeticSubtract(ln, lhs, rhs)
        elif operator == "*":
            return ArithmeticMultiply(ln, lhs, rhs)
        elif operator == "/":
            return ArithmeticDivide(ln, lhs, rhs)
        elif operator == "%":
            return ArithmeticModulo(ln, lhs, rhs)
        else:
            logger.error(f"{ln}: Bad expression")
            self.status = False
            return Node(ln, [])

    # Unary temporal expressions
    @_("TL_GLOBAL interval expr",
       "TL_FUTURE interval expr",
       "TL_HIST interval expr",
       "TL_ONCE interval expr")
    def expr(self, p):
        ln = p.lineno
        operator = p[0]

        if operator == "G":
            return Global(ln, p[2], p[1].lb, p[1].ub)
        elif operator == "F":
            return Future(ln, p[2], p[1].lb, p[1].ub)
        elif operator == "H":
            return Historical(ln, p[2], p[1].lb, p[1].ub)
        elif operator == "O":
            return Once(ln, p[2], p[1].lb, p[1].ub)
        else:
            logger.error(f"{ln}: Bad expression")
            self.status = False
            return Node(ln, [])

    # Binary temporal expressions
    @_("expr TL_UNTIL interval expr",
       "expr TL_RELEASE interval expr",
       "expr TL_SINCE interval expr")
    def expr(self, p):
        ln = p.lineno
        operator = p[1]

        if operator == "U":
            return Until(ln, p[0], p[3], p[2].lb, p[2].ub)
        elif operator == "R":
            return Release(ln, p[0], p[3], p[2].lb, p[2].ub)
        elif operator == "S":
            return Since(ln, p[0], p[3], p[2].lb, p[2].ub)
        else:
            logger.error(f"{ln}: Bad expression")
            self.status = False
            return Node(ln, [])

    # Parentheses
    @_("LPAREN expr RPAREN")
    def expr(self, p):
        return p[1]

    # Symbol
    @_("SYMBOL")
    def expr(self, p):
        ln = p.lineno
        symbol = p.SYMBOL

        if symbol == "true":
            return Bool(ln, True)
        elif symbol == "false":
            return Bool(ln, False)
        elif symbol in self.defs.keys():
            return self.defs[symbol]
        elif symbol in self.vars.keys():
            return Signal(ln, symbol, self.vars[symbol])
        elif symbol in self.atomics.keys():
            return Atomic(ln, symbol)
        else:
            logger.error(f"{ln}: Variable \"{symbol}\" undefined")
            self.status = False
            return Node(ln, [])

    # Integer
    @_("INT")
    def expr(self, p):
        return Integer(p.lineno, int(p.INT))

    # Float
    @_("FLOAT")
    def expr(self, p):
        return Float(p.lineno, float(p.FLOAT))
        
    # Shorthand interval
    @_("LBRACK INT RBRACK")
    def interval(self, p):
        return Interval(0, int(p[1]))

    # Standard interval
    @_("LBRACK INT COMMA INT RBRACK")
    def interval(self, p):
        return Interval(int(p[1]), int(p[3]))
