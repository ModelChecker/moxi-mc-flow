#type: ignore
from typing import Optional
import pathlib

from src import preprocess_smv, sly, log, smv

FILE_NAME = pathlib.Path(__file__).name

class Lexer(sly.Lexer):
    def __init__(self, filename: str) -> None:
        self.filename = filename

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
        SMV_XOR, SMV_XNOR,
        EQUAL, NOTEQUAL,
        LSHIFT, RSHIFT,
        LESSTHAN, LESSEQUAL,
        GREATERTHAN, GREATEREQUAL,
        SMV_MOD,
        SMV_UNION, SMV_IN,
        CONCAT,

        SMV_CASE, SMV_ESAC,

        WORDCONSTANT,

        # primitives
        IDENT, INTEGER, DECIMAL,

        # main keywords
        SMV_MODULE,
        SMV_VAR, SMV_IVAR, SMV_FROZENVAR,
        SMV_FUN, SMV_DEFINE, SMV_CONSTANTS, SMV_ASSIGN, 
        SMV_INIT, SMV_TRANS, SMV_INVAR,
        SMV_FAIRNESS, SMV_JUSTICE, SMV_COMPASSION,
        SMV_PRED, SMV_MIRROR, SMV_ISA, # don't care
        SMV_CTLSPEC, SMV_SPEC, SMV_NAME, # don't care
        SMV_LTLSPEC, SMV_INVARSPEC, SMV_PANDASPEC, 

        # type specifiers
        SMV_INTEGER, SMV_BOOLEAN,
        SMV_WORD, SMV_SIGNED, SMV_UNSIGNED,
        SMV_REAL, SMV_CLOCK,
        SMV_ARRAY, OF,

        SMALLINIT, NEXT,
        PLUS, MINUS, DIVIDE,

        SMV_FALSE, SMV_TRUE,

        SMV_X, SMV_G, SMV_F,
        SMV_Y, SMV_Z, SMV_H,
        SMV_O, SMV_U, SMV_V,
        SMV_S, SMV_T
    }

    ignore = " \t"
    ignore_comment = r"--.*"
    ignore_newline = r"\n+"
    
    WORDCONSTANT = r"0[us]?[bBoOdDhH][0-9]+?_[0-9a-fA-F]+"
    DECIMAL      = r"(0|[1-9]\d*)\.0*(0|[1-9]\d*)"
    INTEGER      = r'-?[0-9][0-9]*'

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
    IDENT = r'[a-zA-Z_][a-zA-Z_0-9#$]*|"[^\\"]*"'

    # main keywords
    IDENT["MODULE"] = SMV_MODULE
    IDENT["VAR"] = SMV_VAR
    IDENT["IVAR"] = SMV_IVAR
    IDENT["FROZENVAR"] = SMV_FROZENVAR
    IDENT["FUN"] = SMV_FUN
    IDENT["DEFINE"] = SMV_DEFINE
    IDENT["CONSTANTS"] = SMV_CONSTANTS
    IDENT["ASSIGN"] = SMV_ASSIGN
    IDENT["INIT"] = SMV_INIT
    IDENT["TRANS"] = SMV_TRANS
    IDENT["INVAR"] = SMV_INVAR
    IDENT["FAIRNESS"] = SMV_FAIRNESS
    IDENT["JUSTICE"] = SMV_JUSTICE
    IDENT["COMPASSION"] = SMV_COMPASSION
    IDENT["PRED"] = SMV_PRED
    IDENT["MIRROR"] = SMV_MIRROR
    IDENT["ISA"] = SMV_ISA
    IDENT["CTLSPEC"] = SMV_CTLSPEC
    IDENT["SPEC"] = SMV_SPEC
    IDENT["NAME"] = SMV_NAME
    IDENT["INVARSPEC"] = SMV_INVARSPEC
    IDENT["LTLSPEC"] = SMV_LTLSPEC
    IDENT["__PANDASPEC__"] = SMV_PANDASPEC # see panda.py

    # type specifiers
    IDENT["integer"] = SMV_INTEGER
    IDENT["boolean"] = SMV_BOOLEAN
    IDENT["unsigned"] = SMV_UNSIGNED
    IDENT["signed"] = SMV_SIGNED
    IDENT["word"] = SMV_WORD
    IDENT["real"] = SMV_REAL
    # IDENT["clock"] = SMV_CLOCK
    IDENT["array"] = SMV_ARRAY
    IDENT["of"] = OF

    # speciall expressions
    IDENT["init"] = SMALLINIT
    IDENT["next"] = NEXT

    IDENT["FALSE"] = SMV_FALSE
    IDENT["TRUE"] = SMV_TRUE

    IDENT["xor"] = SMV_XOR
    IDENT["xnor"] = SMV_XNOR
    IDENT["mod"] = SMV_MOD

    IDENT["union"] = SMV_UNION
    IDENT["in"] = SMV_IN

    IDENT["case"] = SMV_CASE
    IDENT["esac"] = SMV_ESAC

    IDENT["X"] = SMV_X
    IDENT["G"] = SMV_G
    IDENT["F"] = SMV_F
    IDENT["Y"] = SMV_Y
    IDENT["Z"] = SMV_Z
    IDENT["H"] = SMV_H
    IDENT["O"] = SMV_O
    IDENT["U"] = SMV_U
    IDENT["V"] = SMV_V
    IDENT["S"] = SMV_S
    IDENT["T"] = SMV_T

    # Extra action for newlines
    def ignore_newline(self, t):
        self.lineno += t.value.count("\n")

    def error(self, t):
        loc = log.FileLocation(self.filename, self.lineno)
        log.error(f"{self.lineno}: Illegal character \"%s\" {t.value[0]}", FILE_NAME, loc)
        self.index += 1


class Parser(sly.Parser):
    tokens = Lexer.tokens
    def __init__(self, filename: str) -> None:
        super().__init__()
        self.filename = filename
        self.status = True
        self.enums = {}
        self.cur_formula_id = 0

    def loc(self, token) -> log.FileLocation:
        return log.FileLocation(self.filename, token.lineno)

    def error(self, token):
        self.status = False
        log.error(f"Unexpected token ({token})", FILE_NAME, self.loc(token)) 

    precedence = (
        ("left", RIGHTARROW, LEFTRIGHTARROW),
        ("left", BAR),
        ("left", AMPERSAND),
        ("left", SMV_U, SMV_V, SMV_S, SMV_T),
        ("left", SMV_XOR),
        ("left", EQUAL, NOTEQUAL),
        ("left", GREATERTHAN, GREATEREQUAL, LESSTHAN, LESSEQUAL),
        ("left", LSHIFT, RSHIFT),
        ("left", PLUS, MINUS),
        ("left", STAR, DIVIDE, SMV_MOD),
        ("right", EXCLAMATION, UMINUS, SMV_X, SMV_G, SMV_F, SMV_Y, SMV_Z, SMV_H, SMV_O),
        ("right", LPAREN, DOT)
    )

    
    @_("module_list")
    def xmv_program(self, p):
        main = [m for m in p[0] if m.name == "main"]

        if len(main) == 1:
            main = main[0]
        elif len(main) < 1:
            main = None
        elif len(main) > 1:
            log.error(f"Multiple 'main' modules defined.", FILE_NAME)
            self.status = False
            return None

        return smv.Program(modules=p[0], main=main)


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
        "SMV_MODULE IDENT LPAREN parameter_list RPAREN module_body",
        "SMV_MODULE IDENT module_body",
        "SMV_MODULE IDENT LPAREN RPAREN module_body"
    )
    def module(self, p):
        if len(p) == 6:
            return smv.ModuleDeclaration(name=p[1], parameters=p.parameter_list, elements=p.module_body)
        else:
            return smv.ModuleDeclaration(name=p[1], parameters=[], elements=p.module_body)
    

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
        "SMV_VAR var_list",
        "SMV_IVAR var_list",
        "SMV_FROZENVAR var_list",
        "SMV_FUN function_declaration_list",
        "SMV_DEFINE define_body",
        "SMV_CONSTANTS constants_body SEMICOLON",
        "SMV_ASSIGN assign_list",
        "SMV_TRANS expr",
        "SMV_TRANS expr SEMICOLON",
        "SMV_INIT expr",
        "SMV_INIT expr SEMICOLON",
        "SMV_INVAR expr",
        "SMV_INVAR expr SEMICOLON",
        "SMV_JUSTICE expr",
        "SMV_JUSTICE expr SEMICOLON",
        # not dealing with INVAR simple_expr -> simple_expr
        "SMV_INVARSPEC expr",
        "SMV_INVARSPEC expr SEMICOLON",
        "SMV_INVARSPEC SMV_NAME IDENT COLONEQ expr",
        "SMV_INVARSPEC SMV_NAME IDENT COLONEQ expr SEMICOLON",
        "SMV_FAIRNESS expr",
        "SMV_FAIRNESS expr SEMICOLON",
        "SMV_LTLSPEC ltl_expr",
        "SMV_LTLSPEC ltl_expr SEMICOLON",
        "SMV_LTLSPEC SMV_NAME IDENT COLONEQ ltl_expr",
        "SMV_LTLSPEC SMV_NAME IDENT COLONEQ ltl_expr SEMICOLON",
        "SMV_PANDASPEC expr",
        "SMV_PANDASPEC expr SEMICOLON",
        "SMV_PANDASPEC SMV_NAME IDENT COLONEQ expr",
        "SMV_PANDASPEC SMV_NAME IDENT COLONEQ expr SEMICOLON"
    )
    def module_element(self, p):
        match p[0]:
            case "VAR":
                return smv.VarDeclaration(p[1], "VAR")
            case "IVAR":
                return smv.VarDeclaration(p[1], "IVAR")
            case "FROZENVAR":
                return smv.VarDeclaration(p[1], "FROZENVAR")
            case "FUN":
                return smv.FunctionDeclaration(function_list=p[1])
            case "DEFINE":
                return smv.DefineDeclaration(define_list=p[1])
            case "CONSTANTS":
                return smv.ConstantsDeclaration(constants_list=p[1])
            case "ASSIGN":
                return smv.AssignDeclaration(assign_list=p[1])
            case "TRANS":
                return smv.TransDeclaration(formula=p[1])
            case "INIT":
                return smv.InitDeclaration(formula=p[1])
            case "INVAR":
                return smv.InvarDeclaration(formula=p[1])
            case "JUSTICE":
                return smv.JusticeDeclaration(formula=p[1])
            case "INVARSPEC":
                return smv.InvarspecDeclaration(formula=p.expr)
            case "FAIRNESS":
                return smv.FairnessDeclaration(formula=p.expr)
            case "JUSTICE":
                return smv.FairnessDeclaration(formula=p.expr)
            case "LTLSPEC":
                ltlspec = smv.LTLSpecDeclaration(formula=p.ltl_expr, name=f"LTLSPEC_{self.cur_formula_id}")
                self.cur_formula_id += 1
                return ltlspec
            case "__PANDASPEC__":
                return smv.PandaSpecDeclaration(formula=p.expr)
            

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
                return smv.Assign(lhs=p.complex_identifier, rhs=p.expr, modifier="init")
            case "next":
                return smv.Assign(lhs=p.complex_identifier, rhs=p.expr, modifier="next")
            case _:
                return smv.Assign(lhs=p.complex_identifier, rhs=p.expr, modifier="none")

            
    @_("constants_body COMMA complex_identifier", "complex_identifier")
    def constants_body(self, p):
        if len(p) == 1:
            return [smv.Constants(identifier=p[0])]
        else:
            return p[0] + [smv.Constants(identifier=p[2])]

    @_(
        "define_body complex_identifier COLONEQ expr SEMICOLON",
        "complex_identifier COLONEQ expr SEMICOLON"
    )    
    def define_body(self, p):
        if len(p) == 4:
            return [smv.Define(name=p.complex_identifier, expr=p.expr)]
        else:
            return p.define_body + [smv.Define(name=p.complex_identifier, expr=p.expr)]
        
    @_(
        "constant",
        "complex_identifier",
        "LPAREN expr RPAREN",
        "MINUS expr %prec UMINUS",
        "EXCLAMATION expr %prec UMINUS",
        "expr AMPERSAND expr",
        "expr BAR expr",
        "expr SMV_XOR expr",
        "expr SMV_XNOR expr",
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
        "expr SMV_MOD expr",
        "expr LSHIFT expr",
        "expr RSHIFT expr",
        "expr SMV_UNION expr",
        "expr SMV_IN expr",
        "IDENT LPAREN cs_expr_list RPAREN",
        "SMV_UNSIGNED SMV_WORD LBRACK INTEGER RBRACK expr",
        "SMV_SIGNED SMV_WORD LBRACK INTEGER RBRACK expr"
    )
    def expr(self, p):
        if len(p) == 1: # constants/whatever
            return p[0]
        if len(p) == 2: # unop
            return smv.UnOp(op=p[0], arg=p[1], loc=self.loc(p))
        if p[0] == "(":
            return p[1]
        if len(p) == 3: # binop
            return smv.BinOp(op=p[1], lhs=p[0], rhs=p[2], loc=self.loc(p)) 
        if len(p) == 4: # function call
            return smv.FunCall(name=p[0], args=p.cs_expr_list, loc=self.loc(p))
        if p[1] == "word":
            width = smv.IntegerConstant(int(p[3]))
            arg = p[5]
            return smv.FunCall(name=f"{p[0]} {p[1]}", args=[width, arg], loc=self.loc(p))
        
    @_("NEXT LPAREN expr RPAREN")
    def expr(self, p):
        return smv.FunCall(name="next", args=[p[2]], loc=self.loc(p))
    
    @_("SMV_SIGNED LPAREN expr RPAREN")
    def expr(self, p):
        return smv.FunCall(name="signed", args=[p[2]], loc=self.loc(p))
    
    @_("SMV_UNSIGNED LPAREN expr RPAREN")
    def expr(self, p):
        return smv.FunCall(name="unsigned", args=[p[2]], loc=self.loc(p))

    @_("expr LBRACK expr RBRACK")
    def expr(self, p):
        return smv.IndexSubscript(array=p[0], index=p[2], loc=self.loc(p))

    @_("expr LBRACK INTEGER COLON INTEGER RBRACK")
    def expr(self, p):
        return smv.WordBitSelection(word=p[0], high=int(p[2]), low=int(p[4]), loc=self.loc(p))

    @_("expr CONCAT expr")
    def expr(self, p):
        return smv.BinOp(op="concat", lhs=p[0], rhs=p[2], loc=self.loc(p))
    
    @_("LBRACE cs_expr_list RBRACE")
    def expr(self, p):
        return smv.SetBodyExpression(members=p.cs_expr_list, loc=self.loc(p))
    
    @_("expr QUESTIONMARK expr COLON expr")
    def expr(self, p):
        return smv.Ternary(cond=p[0], then_expr=p[2], else_expr=p[4], loc=self.loc(p))
    
    @_("case_expr")
    def expr(self, p):
        return p[0]
    
    @_(
        "ltl_prop_expr",
        "LPAREN ltl_expr RPAREN",
        "EXCLAMATION ltl_expr %prec UMINUS",
        "SMV_X ltl_expr",
        "SMV_G ltl_expr",
        "SMV_F ltl_expr",
        "SMV_Y ltl_expr",
        "SMV_Z ltl_expr",
        "SMV_H ltl_expr",
        "SMV_O ltl_expr",
        "ltl_expr AMPERSAND ltl_expr",
        "ltl_expr BAR ltl_expr",
        "ltl_expr SMV_XOR ltl_expr",
        "ltl_expr SMV_XNOR ltl_expr",
        "ltl_expr RIGHTARROW ltl_expr",
        "ltl_expr LEFTRIGHTARROW ltl_expr",
        "ltl_expr SMV_U ltl_expr",
        "ltl_expr SMV_V ltl_expr",
        "ltl_expr SMV_S ltl_expr",
        "ltl_expr SMV_T ltl_expr",
    )
    def ltl_expr(self, p):
        if len(p) == 1: 
            return smv.LTLProposition(p[0], loc=self.loc(p))
        if len(p) == 2: # unop
            return smv.UnOp(op=p[0], arg=p[1], loc=self.loc(p))
        if p[0] == "(":
            return p[1]
        if len(p) == 3: # binop
            return smv.BinOp(op=p[1], lhs=p[0], rhs=p[2], loc=self.loc(p)) 
        if len(p) == 4: # function call
            return smv.FunCall(name=p[0], args=p.cs_expr_list, loc=self.loc(p))
        
    @_(
        "constant",
        "complex_identifier",
        "LPAREN ltl_prop_expr RPAREN",
        "MINUS ltl_prop_expr %prec UMINUS",
        "ltl_prop_expr EQUAL ltl_prop_expr",
        "ltl_prop_expr NOTEQUAL ltl_prop_expr",
        "ltl_prop_expr LESSTHAN ltl_prop_expr",
        "ltl_prop_expr GREATEREQUAL ltl_prop_expr",
        "ltl_prop_expr GREATERTHAN ltl_prop_expr",
        "ltl_prop_expr LESSEQUAL ltl_prop_expr",
        "ltl_prop_expr PLUS ltl_prop_expr",
        "ltl_prop_expr MINUS ltl_prop_expr",
        "ltl_prop_expr STAR ltl_prop_expr",
        "ltl_prop_expr DIVIDE ltl_prop_expr",
        "ltl_prop_expr SMV_MOD ltl_prop_expr",
        "ltl_prop_expr LSHIFT ltl_prop_expr",
        "ltl_prop_expr RSHIFT ltl_prop_expr",
        "ltl_prop_expr SMV_UNION ltl_prop_expr",
        "ltl_prop_expr SMV_IN ltl_prop_expr",
        "IDENT LPAREN cs_expr_list RPAREN"
    )
    def ltl_prop_expr(self, p):
        if len(p) == 1: # constants/whatever
            return p[0]
        if len(p) == 2: # unop
            return smv.UnOp(op=p[0], arg=p[1], loc=self.loc(p))
        if p[0] == "(":
            return p[1]
        if len(p) == 3: # binop
            return smv.BinOp(op=p[1], lhs=p[0], rhs=p[2], loc=self.loc(p)) 
        if len(p) == 4: # function call
            return smv.FunCall(name=p[0], args=p.cs_expr_list, loc=self.loc(p))
        
    @_("NEXT LPAREN ltl_prop_expr RPAREN")
    def ltl_prop_expr(self, p):
        return smv.FunCall(name="next", args=[p[2]], loc=self.loc(p))
    
    @_("SMV_SIGNED LPAREN ltl_prop_expr RPAREN")
    def ltl_prop_expr(self, p):
        return smv.FunCall(name="signed", args=[p[2]], loc=self.loc(p))
    
    @_("SMV_UNSIGNED LPAREN ltl_prop_expr RPAREN")
    def ltl_prop_expr(self, p):
        return smv.FunCall(name="unsigned", args=[p[2]], loc=self.loc(p))

    @_("ltl_prop_expr LBRACK ltl_prop_expr RBRACK")
    def ltl_prop_expr(self, p):
        return smv.IndexSubscript(array=p[0], index=p[2], loc=self.loc(p))

    @_("ltl_prop_expr LBRACK INTEGER COLON INTEGER RBRACK")
    def ltl_prop_expr(self, p):
        return smv.WordBitSelection(word=p[0], high=int(p[2]), low=int(p[4]), loc=self.loc(p))

    @_("ltl_prop_expr CONCAT ltl_prop_expr")
    def ltl_prop_expr(self, p):
        return smv.BinOp(op="concat", lhs=p[0], rhs=p[2], loc=self.loc(p))
    
    @_("LBRACE cs_expr_list RBRACE")
    def ltl_prop_expr(self, p):
        return smv.SetBodyExpression(members=p.cs_expr_list, loc=self.loc(p))
    
    @_("ltl_prop_expr QUESTIONMARK ltl_prop_expr COLON ltl_prop_expr")
    def ltl_prop_expr(self, p):
        return smv.Ternary(cond=p[0], then_expr=p[2], else_expr=p[4], loc=self.loc(p))
    
    @_("case_expr")
    def ltl_prop_expr(self, p):
        return p[0]
    
    @_("SMV_CASE case_body SMV_ESAC")
    def case_expr(self, p):
        return smv.CaseExpr(branches=p[1], loc=self.loc(p))
    
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

    @_("IDENT COLON function_domain RIGHTARROW type_specifier SEMICOLON")
    def function_declaration(self, p):
        return smv.Function(name=p[0], type=(p.function_domain, p.type_specifier))
    
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
        return smv.ModuleAccess(p[0], smv.Identifier(p[2]), loc=self.loc(p))

    @_("IDENT")
    def complex_identifier(self, p):
        return smv.Identifier(p[0], loc=self.loc(p))
    
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
        "SMV_BOOLEAN", 
        "SMV_INTEGER", 
        "SMV_WORD LBRACK INTEGER RBRACK",
        "SMV_UNSIGNED SMV_WORD LBRACK INTEGER RBRACK",
        "SMV_SIGNED SMV_WORD LBRACK INTEGER RBRACK",
        "SMV_REAL",
        "SMV_CLOCK",
        "LBRACE enumeration_type_body RBRACE",
        "INTEGER DOT DOT INTEGER",
        "SMV_ARRAY OF INTEGER DOT DOT INTEGER OF type_specifier",
        "SMV_ARRAY SMV_WORD LBRACK INTEGER RBRACK OF type_specifier",
        "IDENT LPAREN cs_expr_list RPAREN",
        "IDENT LPAREN RPAREN",
        "IDENT LPAREN constant_list RPAREN"
    )
    def type_specifier(self, p):
        match p[0]:
            case "boolean":
                return smv.Boolean()
            case "integer":
                return smv.Integer()
            case "word":
                return smv.Word(width=int(p[2]), signed=False)
            case "unsigned":
                return smv.Word(width=int(p[3]), signed=False)
            case "signed":
                return smv.Word(width=int(p[3]), signed=True)
            case "real":
                return smv.Real()
            # case "clock":
            #     return nuxmv.Clock()
            case "{":
                return smv.Enumeration(summands=p[1])
            case "array":
                if p[1] == "word":
                    return smv.WordArray(word_length=int(p[3]), subtype=p.type_specifier)
                else:
                    return smv.Array(low=p[2], high=int(p[5]), subtype=int(p[7]))
            case _:
                def is_int(n : str):
                    try:
                        int(n)
                    except ValueError:
                        return False
                    else:
                        return True


                if is_int(p[0]):
                    return smv.Enumeration(summands=set(range(int(p[0]), int(p[3]))))
                elif len(p) == 3:
                    return smv.ModuleType(module_name=p[0], parameters=[])
                else:
                    return smv.ModuleType(module_name=p[0], parameters=p[2])
    
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
        "real_constant",
        "symbolic_constant",
        "word_constant",
        "range_constant"
    )
    def constant(self, p):
        return p[0]
    
    @_("SMV_FALSE", "SMV_TRUE")
    def boolean_constant(self, p):
        match p[0]:
            case "FALSE":
                return smv.BooleanConstant(boolean=False, loc=self.loc(p))
            case "TRUE":
                return smv.BooleanConstant(boolean=True, loc=self.loc(p))
            
    @_("INTEGER")
    def integer_constant(self, p):
        return smv.IntegerConstant(integer=int(p[0]), loc=self.loc(p))
            
    @_("DECIMAL")
    def real_constant(self, p):
        return smv.RealConstant(real=float(p[0]), loc=self.loc(p))
    
    @_("complex_identifier")
    def symbolic_constant(self, p):
        return smv.SymbolicConstant(symbol=p[0], loc=self.loc(p))
    
    @_("INTEGER DOT DOT INTEGER")
    def range_constant(self, p):
        return smv.RangeConstant(low=int(p[0]), high=int(p[3]), loc=self.loc(p))
    
    @_("WORDCONSTANT")
    def word_constant(self, p):
        return smv.WordConstant(p[0], loc=self.loc(p))

        
def parse(input_path: pathlib.Path, do_cpp: bool) -> Optional[smv.Program]:
    content = preprocess_smv.preprocess(input_path, do_cpp)

    log.debug(2, f"Parsing {input_path}", FILE_NAME)

    lexer = Lexer(input_path.name)
    parser = Parser(input_path.name)

    result = parser.parse(lexer.tokenize(content))

    return (result if parser.status else None)
