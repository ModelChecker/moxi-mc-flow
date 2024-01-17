#type: ignore
from typing import Optional
from pathlib import Path

from .sly import Lexer, Parser
from .preprocess_nuxmv import preprocess
from .nuxmv import *
from .util import logger

class NuXmvLexer(Lexer):
    tokens = { 
        # punctuation
        COMMA, DOT, STAR,
        RIGHTARROW, LEFTRIGHTARROW,

        COLON, SEMICOLON,
        LPAREN, RPAREN,
        LBRACE, RBRACE,
        LBRACK, RBRACK,
        COLONEQ,

        # expressions
        EXCLAMATION, QUESTIONMARK,
        AMPERSAND, BAR,
        XMV_XOR, XMV_XNOR,
        EQUAL, NOTEQUAL,
        LSHIFT, RSHIFT,
        LESSTHAN, LESSEQUAL,
        GREATERTHAN, GREATEREQUAL,
        XMV_MOD,
        XMV_UNION, XMV_IN,
        CONCAT,

        XMV_CASE, XMV_ESAC,

        WORDCONSTANT,

        # primitives
        IDENT, INTEGER,

        # main keywords
        XMV_MODULE,
        XMV_VAR, XMV_IVAR, XMV_FROZENVAR,
        XMV_FUN, XMV_DEFINE, XMV_CONSTANTS, XMV_ASSIGN, 
        XMV_INIT, XMV_TRANS, XMV_INVAR,
        XMV_FAIRNESS, XMV_JUSTICE, XMV_COMPASSION,
        XMV_PRED, XMV_MIRROR, XMV_ISA, # don't care
        XMV_CTLSPEC, XMV_SPEC, XMV_NAME, # don't care
        XMV_LTLSPEC, XMV_INVARSPEC,

        # type specifiers
        XMV_INTEGER, XMV_BOOLEAN,
        XMV_WORD, XMV_SIGNED, XMV_UNSIGNED,
        XMV_REAL, XMV_CLOCK,
        XMV_ARRAY, OF,

        SMALLINIT, NEXT,
        PLUS, MINUS, DIVIDE,

        XMV_FALSE, XMV_TRUE,

        XMV_X, XMV_G, XMV_F,
        XMV_Y, XMV_Z, XMV_H,
        XMV_O, XMV_U, XMV_V,
        XMV_S, XMV_T
    }

    ignore = " \t"
    ignore_comment = r"--.*"
    ignore_newline = r"\n+"
    
    WORDCONSTANT = r"0[us]?[bBoOdDhH][0-9]+?_[0-9a-fA-F]+"
    INTEGER = r'-?[0-9][0-9]*'

    # punctuation
    COLONEQ = r"\:\="
    NOTEQUAL = r"\!\="
    COMMA = r"\,"
    CONCAT = r"\:\:"
    COLON = r"\:"
    SEMICOLON = r"\;"
    DOT = r"\."
    STAR = r"\*"
    EXCLAMATION = r"\!"
    QUESTIONMARK = r"\?"
    AMPERSAND = r"\&"
    BAR = r"\|"
    RIGHTARROW = r"\-\>"
    LEFTRIGHTARROW = r"\<\-\>"
    EQUAL = r"\="
    PLUS = r"\+"
    MINUS = r"\-"
    DIVIDE = r"\/"

    # goes before LESSTHAN/GREATERTHAN
    LSHIFT = r"\>\>"
    RSHIFT = r"\<\<"


    LESSEQUAL = r"\<\="
    GREATEREQUAL= r"\>\="
    LESSTHAN = r"\<"
    GREATERTHAN = r"\>"

    LPAREN = r"\("
    RPAREN = r"\)"
    LBRACE = r"\{"
    RBRACE = r"\}"
    LBRACK = r"\["
    RBRACK = r"\]"


    # primitives
    IDENT = r'[a-zA-Z_][a-zA-Z_0-9#$]*'

    # main keywords
    IDENT["MODULE"] = XMV_MODULE
    IDENT["VAR"] = XMV_VAR
    IDENT["IVAR"] = XMV_IVAR
    IDENT["FROZENVAR"] = XMV_FROZENVAR
    IDENT["FUN"] = XMV_FUN
    IDENT["DEFINE"] = XMV_DEFINE
    IDENT["CONSTANTS"] = XMV_CONSTANTS
    IDENT["ASSIGN"] = XMV_ASSIGN
    IDENT["INIT"] = XMV_INIT
    IDENT["TRANS"] = XMV_TRANS
    IDENT["INVAR"] = XMV_INVAR
    IDENT["FAIRNESS"] = XMV_FAIRNESS
    IDENT["JUSTICE"] = XMV_JUSTICE
    IDENT["COMPASSION"] = XMV_COMPASSION
    IDENT["PRED"] = XMV_PRED
    IDENT["MIRROR"] = XMV_MIRROR
    IDENT["ISA"] = XMV_ISA
    IDENT["CTLSPEC"] = XMV_CTLSPEC
    IDENT["SPEC"] = XMV_SPEC
    IDENT["NAME"] = XMV_NAME
    IDENT["INVARSPEC"] = XMV_INVARSPEC
    IDENT["LTLSPEC"] = XMV_LTLSPEC

    # type specifiers
    IDENT["integer"] = XMV_INTEGER
    IDENT["boolean"] = XMV_BOOLEAN
    IDENT["unsigned"] = XMV_UNSIGNED
    IDENT["signed"] = XMV_SIGNED
    IDENT["word"] = XMV_WORD
    IDENT["real"] = XMV_REAL
    # IDENT["clock"] = XMV_CLOCK
    IDENT["array"] = XMV_ARRAY
    IDENT["of"] = OF

    # speciall expressions
    IDENT["init"] = SMALLINIT
    IDENT["next"] = NEXT

    IDENT["FALSE"] = XMV_FALSE
    IDENT["TRUE"] = XMV_TRUE

    IDENT["xor"] = XMV_XOR
    IDENT["xnor"] = XMV_XNOR
    IDENT["mod"] = XMV_MOD

    IDENT["union"] = XMV_UNION
    IDENT["in"] = XMV_IN

    IDENT["case"] = XMV_CASE
    IDENT["esac"] = XMV_ESAC

    IDENT["X"] = XMV_X
    IDENT["G"] = XMV_G
    IDENT["F"] = XMV_F
    IDENT["Y"] = XMV_Y
    IDENT["Z"] = XMV_Z
    IDENT["H"] = XMV_H
    IDENT["O"] = XMV_O
    IDENT["U"] = XMV_U
    IDENT["V"] = XMV_V
    IDENT["S"] = XMV_S
    IDENT["T"] = XMV_T

    # Extra action for newlines
    def ignore_newline(self, t):
        self.lineno += t.value.count("\n")


class NuXmvParser(Parser):
    tokens = NuXmvLexer.tokens

    def __init__(self):
        super().__init__()
        self.status = True
        self.enums = {}

    def error(self, token):
        self.status = False
        logger.error(f"Unexpected token ({token})") 

    precedence = (
        ("left", RIGHTARROW, LEFTRIGHTARROW),
        ("left", BAR),
        ("left", AMPERSAND),
        ("left", XMV_U, XMV_V, XMV_S, XMV_T),
        ("left", XMV_XOR),
        ("left", EQUAL, NOTEQUAL),
        ("left", GREATERTHAN, GREATEREQUAL, LESSTHAN, LESSEQUAL),
        ("left", LSHIFT, RSHIFT),
        ("left", PLUS, MINUS),
        ("left", STAR, DIVIDE, XMV_MOD),
        ("right", EXCLAMATION, UMINUS, XMV_X, XMV_G, XMV_F, XMV_Y, XMV_Z, XMV_H, XMV_O),
        ("right", LPAREN, DOT)
    )

    
    @_("module_list")
    def xmv_program(self, p):
        main = [m for m in p[0] if m.name == "main"]

        if len(main) < 1:
            logger.error(f"'main' module undefined.")
            self.status = False
        elif len(main) > 1:
            logger.error(f"Multiple 'main' modules defined.")
            self.status = False

        main = main[0]

        return XMVProgram(modules=p[0], main=main)


    @_(
        "module_list module", 
        ""
    )
    def module_list(self, p):
        if len(p) == 0: # base case: empty list of modules
            return []
        else: 
            return p[0] + [p[1]] # recursive case: n+1 modules

    @_(
        "parameter_list COMMA IDENT", 
        "IDENT",
        ""
    )
    def parameter_list(self, p):
        if len(p) == 0:
            return []
        if len(p) == 1: # base case: `(param)`
            return [p[0]]
        return p[0] + [p[2]] # recursive case: `(param1, param2, ...)`
    
    @_(
        "XMV_MODULE IDENT LPAREN parameter_list RPAREN module_body",
        "XMV_MODULE IDENT module_body",
        "XMV_MODULE IDENT LPAREN RPAREN module_body"
    )
    def module(self, p):
        if len(p) == 6:
            return XMVModule(name=p[1], parameters=p.parameter_list, elements=p.module_body)
        else:
            return XMVModule(name=p[1], parameters=[], elements=p.module_body)
    

    @_(
        "module_body module_element", 
        ""
    )
    def module_body(self, p):
        if len(p) == 2:
            return p[0] + [p[1]]
        else:
            return []

    @_(
        "XMV_VAR var_list",
        "XMV_IVAR var_list",
        "XMV_FROZENVAR var_list",
        "XMV_FUN function_declaration_list",
        "XMV_DEFINE define_body",
        "XMV_CONSTANTS constants_body SEMICOLON",
        "XMV_ASSIGN assign_list",
        "XMV_TRANS expr",
        "XMV_TRANS expr SEMICOLON",
        "XMV_INIT expr",
        "XMV_INIT expr SEMICOLON",
        "XMV_INVAR expr",
        "XMV_INVAR expr SEMICOLON",
        # not dealing with INVAR simple_expr -> simple_expr
        "XMV_INVARSPEC expr",
        "XMV_INVARSPEC expr SEMICOLON",
        "XMV_INVARSPEC XMV_NAME IDENT COLONEQ expr",
        "XMV_INVARSPEC XMV_NAME IDENT COLONEQ expr SEMICOLON",
        "XMV_LTLSPEC expr",
        "XMV_LTLSPEC expr SEMICOLON",
        "XMV_LTLSPEC XMV_NAME IDENT COLONEQ expr",
        "XMV_LTLSPEC XMV_NAME IDENT COLONEQ expr SEMICOLON"
    )
    def module_element(self, p):
        match p[0]:
            case "VAR":
                return XMVVarDeclaration(p[1], "VAR")
            case "IVAR":
                return XMVVarDeclaration(p[1], "IVAR")
            case "FROZENVAR":
                return XMVVarDeclaration(p[1], "FROZENVAR")
            case "FUN":
                return XMVFunctionDeclaration(function_list=p[1])
            case "DEFINE":
                return XMVDefineDeclaration(define_list=p[1])
            case "CONSTANTS":
                return XMVConstantsDeclaration(constants_list=p[1])
            case "ASSIGN":
                return XMVAssignDeclaration(assign_list=p[1])
            case "TRANS":
                return XMVTransDeclaration(formula=p[1])
            case "INIT":
                return XMVInitDeclaration(formula=p[1])
            case "INVAR":
                return XMVInvarDeclaration(formula=p[1])
            case "INVARSPEC":
                return XMVInvarspecDeclaration(formula=p.expr)
            case "LTLSPEC":
                return XMVLTLSpecDeclaration(formula=p.expr)

    @_(
            "assign_list assign SEMICOLON",
            "assign SEMICOLON"
    )
    def assign_list(self, p):
        if len(p) == 2:
            return [p[0]]
        else:
            return p[0] + [p[1]]
        
    @_(
        "complex_identifier COLONEQ expr",
        "SMALLINIT LPAREN complex_identifier RPAREN COLONEQ expr",
        "NEXT LPAREN complex_identifier RPAREN COLONEQ expr"
    )
    def assign(self, p):
        match p[0]:
            case "init":
                return XMVAssign(lhs=p.complex_identifier, rhs=p.expr, modifier="init")
            case "next":
                return XMVAssign(lhs=p.complex_identifier, rhs=p.expr, modifier="next")
            case _:
                return XMVAssign(lhs=p.complex_identifier, rhs=p.expr, modifier="none")

            
    @_("constants_body COMMA complex_identifier", "complex_identifier")
    def constants_body(self, p):
        if len(p) == 1:
            return [XMVConstants(identifier=p[0])]
        else:
            return p[0] + [XMVConstants(identifier=p[2])]

    @_(
        "define_body complex_identifier COLONEQ expr SEMICOLON",
        "complex_identifier COLONEQ expr SEMICOLON"
    )    
    def define_body(self, p):
        if len(p) == 4:
            return [XMVDefine(name=p.complex_identifier, expr=p.expr)]
        else:
            return p.define_body + [XMVDefine(name=p.complex_identifier, expr=p.expr)]
        
    @_(
        "constant",
        "complex_identifier",
        "LPAREN expr RPAREN",
        "MINUS expr %prec UMINUS",
        "EXCLAMATION expr %prec UMINUS",
        "XMV_X expr",
        "XMV_G expr",
        "XMV_F expr",
        "XMV_Y expr",
        "XMV_Z expr",
        "XMV_H expr",
        "XMV_O expr",
        "expr AMPERSAND expr",
        "expr BAR expr",
        "expr XMV_XOR expr",
        "expr XMV_XNOR expr",
        "expr RIGHTARROW expr",
        "expr LEFTRIGHTARROW expr",
        "expr EQUAL expr",
        "expr NOTEQUAL expr",
        "expr LESSTHAN expr",
        "expr GREATEREQUAL expr",
        "expr GREATERTHAN expr",
        "expr LESSEQUAL expr",
        "expr PLUS expr",
        "expr MINUS expr",
        "expr STAR expr",
        "expr DIVIDE expr",
        "expr XMV_MOD expr",
        "expr LSHIFT expr",
        "expr RSHIFT expr",
        "expr XMV_UNION expr",
        "expr XMV_IN expr",
        "expr XMV_U expr",
        "expr XMV_V expr",
        "expr XMV_S expr",
        "expr XMV_T expr",
        "IDENT LPAREN cs_expr_list RPAREN"
    )
    def expr(self, p):
        if len(p) == 1: # TODO: constants/whatever
            return p[0]
        if len(p) == 2: # unop
            return XMVUnOp(op=p[0], arg=p[1])
        if p[0] == "(":
            return p[1]
        if len(p) == 3: # binop
            return XMVBinOp(op=p[1], lhs=p[0], rhs=p[2]) 
        if len(p) == 4: # function call
            return XMVFunCall(name=p[0], args=p.cs_expr_list)
        
    @_("NEXT LPAREN expr RPAREN")
    def expr(self, p):
        return XMVFunCall(name="next", args=[p[2]])
    
    @_("XMV_SIGNED LPAREN expr RPAREN")
    def expr(self, p):
        return XMVFunCall(name="signed", args=[p[2]])
    
    @_("XMV_UNSIGNED LPAREN expr RPAREN")
    def expr(self, p):
        return XMVFunCall(name="unsigned", args=[p[2]])

    @_("expr LBRACK expr RBRACK")
    def expr(self, p):
        return XMVIndexSubscript(array=p[0], index=p[2])

    @_("expr LBRACK INTEGER COLON INTEGER RBRACK")
    def expr(self, p):
        return XMVWordBitSelection(word=p[0], high=int(p[2]), low=int(p[4]))

    @_("expr CONCAT expr")
    def expr(self, p):
        return XMVBinOp(op="concat", lhs=p[0], rhs=p[2])
    
    @_("LBRACE cs_expr_list RBRACE")
    def expr(self, p):
        return XMVSetBodyExpression(members=p.cs_expr_list)
    
    @_("expr QUESTIONMARK expr COLON expr")
    def expr(self, p):
        return XMVTernary(cond=p[0], then_expr=p[2], else_expr=p[4])
    
    @_("case_expr")
    def expr(self, p):
        return p[0]
    
    @_(
        "constant",
        "complex_identifier",
        "LPAREN expr RPAREN",
        "EXCLAMATION expr %prec UMINUS",
        "XMV_X expr",
        "XMV_G expr",
        "XMV_F expr",
        "XMV_Y expr",
        "XMV_Z expr",
        "XMV_H expr",
        "XMV_O expr",
        "expr AMPERSAND expr",
        "expr BAR expr",
        "expr XMV_XOR expr",
        "expr XMV_XNOR expr",
        "expr RIGHTARROW expr",
        "expr LEFTRIGHTARROW expr",
        "expr LESSEQUAL expr",
        "expr XMV_U expr",
        "expr XMV_V expr",
        "expr XMV_S expr",
        "expr XMV_T expr",
    )
    def ltl_expr(self, p):
        if len(p) == 1: # TODO: constants/whatever
            return p[0]
        if len(p) == 2: # unop
            return XMVUnOp(op=p[0], arg=p[1])
        if p[0] == "(":
            return p[1]
        if len(p) == 3: # binop
            return XMVBinOp(op=p[1], lhs=p[0], rhs=p[2]) 
        if len(p) == 4: # function call
            return XMVFunCall(name=p[0], args=p.cs_expr_list)
    
    @_("XMV_CASE case_body XMV_ESAC")
    def case_expr(self, p):
        return XMVCaseExpr(branches=p[1])
    
    @_("expr COLON expr SEMICOLON", "case_body expr COLON expr SEMICOLON")
    def case_body(self, p):
        if len(p) == 4:
            return [(p[0], p[2])]
        else:
            return p[0] + [(p[1], p[3])]


    @_("cs_expr_list COMMA expr", "expr")
    def cs_expr_list(self, p):
            if len(p) == 1:
                return [p.expr]
            else:
                return p[0] + [p.expr]


    @_("function_declaration_list function_declaration", "function_declaration")
    def function_declaration_list(self, p):
        if len(p) == 1:
            return [p[0]]
        else:
            return p[0] + [p[1]]

    @_("IDENT COLON function_domain RIGHTARROW type_specifier")
    def function_declaration(self, p):
        return XMVFunction(name=p[0], type=(p.function_domain, p.type_specifier))
    
    @_("function_domain STAR type_specifier", "type_specifier")
    def function_domain(self, p):
        if len(p) == 1:
            return [p[0]]
        else:
            return p[0] + [p[2]]


    @_(
        "var_list var_decl", 
       ""
    )
    def var_list(self, p):
        if len(p) == 0:
            return []
        else:
            return p[0] + [p[1]]
 
    @_("complex_identifier COLON type_specifier SEMICOLON")
    def var_decl(self, p):
        return (p[0], p[2])

    @_("complex_identifier DOT IDENT")
    def complex_identifier(self, p):
        return XMVModuleAccess(p[0], XMVIdentifier(p[2]))


    @_("IDENT")
    def complex_identifier(self, p):
        return XMVIdentifier(p[0])
    
    # type specifier rules

    @_(
        "constant_list COMMA constant", 
        "constant"
    )
    def constant_list(self, p):
        if len(p) == 1: # base case: `(param)`
            return [p[0]]
        return p[0] + [p[2]] # recursive case: `(param1, param2, ...)`

    @_(
        "XMV_BOOLEAN", 
        "XMV_INTEGER", 
        "XMV_WORD LBRACK INTEGER RBRACK",
        "XMV_UNSIGNED XMV_WORD LBRACK INTEGER RBRACK",
        "XMV_SIGNED XMV_WORD LBRACK INTEGER RBRACK",
        "XMV_REAL",
        "XMV_CLOCK",
        "LBRACE enumeration_type_body RBRACE",
        "INTEGER DOT DOT INTEGER",
        "XMV_ARRAY OF INTEGER DOT DOT INTEGER OF type_specifier",
        "XMV_ARRAY XMV_WORD LBRACK INTEGER RBRACK OF type_specifier",
        "IDENT LPAREN cs_expr_list RPAREN",
        "IDENT LPAREN constant_list RPAREN"
    )
    def type_specifier(self, p):
        match p[0]:
            case "boolean":
                return XMVBoolean()
            case "integer":
                return XMVInteger()
            case "word":
                return XMVWord(width=int(p[2]), signed=False)
            case "unsigned":
                return XMVWord(width=int(p[3]), signed=False)
            case "signed":
                return XMVWord(width=int(p[3]), signed=True)
            case "real":
                return XMVReal()
            # case "clock":
            #     return XMVClock()
            case "{":
                return XMVEnumeration(summands=p[1])
            case "array":
                if p[1] == "word":
                    return XMVWordArray(word_length=int(p[3]), subtype=p.type_specifier)
                else:
                    return XMVArray(low=p[2], high=int(p[5]), subtype=int(p[7]))
            case _:
                if str.isnumeric(p[0]):
                    return XMVEnumeration(summands=set(range(int(p[0]), int(p[3]))))
                else:
                    return XMVModuleType(module_name=p[0], parameters=p[2])
    
    @_(
        "enumeration_type_body COMMA enumeration_type_value", 
        "enumeration_type_value"
    )
    def enumeration_type_body(self, p):
        if len(p) == 1:
            return [p[0]]
        else:
            return p[0] + [p[2]]
        
    @_("IDENT")
    def enumeration_type_value(self, p):
        return p[0]
        
    @_("INTEGER")
    def enumeration_type_value(self, p):
        return int(p[0])
    
    @_(
        "boolean_constant",
        "integer_constant",
        "symbolic_constant",
        "word_constant",
        "range_constant"
    )
    def constant(self, p):
        return p[0]
    
    @_("XMV_FALSE", "XMV_TRUE")
    def boolean_constant(self, p):
        match p[0]:
            case "FALSE":
                return XMVBooleanConstant(boolean=False)
            case "TRUE":
                return XMVBooleanConstant(boolean=True)
            
    @_("INTEGER")
    def integer_constant(self, p):
        return XMVIntegerConstant(integer=int(p[0]))
    
    @_("complex_identifier")
    def symbolic_constant(self, p):
        return XMVSymbolicConstant(symbol=p[0])
    
    @_("INTEGER DOT DOT INTEGER")
    def range_constant(self, p):
        return XMVRangeConstant(low=int(p[0]), high=int(p[3]))
    
    @_("WORDCONSTANT")
    def word_constant(self, p):
        return XMVWordConstant(p[0])

        
def parse(input_path: Path, do_cpp: bool) -> Optional[XMVProgram]:
    content = preprocess(input_path, do_cpp)

    logger.debug(f"Parsing {input_path}")

    lexer = NuXmvLexer()
    parser = NuXmvParser()

    result = parser.parse(lexer.tokenize(content))

    return (result if parser.status else None)
