#type: ignore
import sys
import glob
import argparse

from sly import Lexer, Parser
from nuxmv import *

import rich

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

        LTLUNOP, LTLBINOP
    }

    ignore = " \t"
    ignore_comment = r"--.*"
    ignore_newline = r"\n+"

    # punctuation
    COLONEQ = r"\:\="
    COMMA = r"\,"
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
    NOTEQUAL = r"\!\="
    PLUS = r"\+"
    MINUS = r"\-"
    DIVIDE = r"\/"

    # goes before LESSTHAN/GREATERTHAN
    LSHIFT = r"\>\>"
    RSHIFT = r"\<\<"


    LESSTHAN = r"\<"
    GREATERTHAN = r"\>"
    LESSEQUAL = r"\<\="
    GREATEREQUAL= r"\>\="

    LPAREN = r"\("
    RPAREN = r"\)"
    LBRACE = r"\{"
    RBRACE = r"\}"
    LBRACK = r"\["
    RBRACK = r"\]"

    WORDCONSTANT = r"0[us]?[bBoOdDhH][0-9]+?_[0-9a-fA-F]+"

    LTLUNOP = r"[XGFYZHO](?=[ \n])"
    LTLBINOP = r"(?<=[ \n])[UVST](?=[ \n])"

    # primitives
    IDENT = r'[a-zA-Z_][a-zA-Z_0-9#$]*'
    INTEGER = r'-?[0-9][0-9]*'



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
    IDENT["clock"] = XMV_CLOCK
    IDENT["array"] = XMV_ARRAY
    IDENT["of"] = OF

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


class NuXmvParser(Parser):
    tokens = NuXmvLexer.tokens

    def __init__(self):
        super().__init__()
        self.status = True
        self.enums = {}

    def error(self, token):
        self.status = False
        sys.stderr.write(f"Error: Unexpected token ({token})") 


    precedence = (
        ('left', PLUS, MINUS),
        ('left', STAR, DIVIDE),
        ('right', UMINUS),
    )
    

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
        "IDENT"
    )
    def parameter_list(self, p):
        if len(p) == 1: # base case: `(param)`
            return [p[0]]
        return p[0] + [p[2]] # recursive case: `(param1, param2, ...)`
    
    @_(
        "XMV_MODULE IDENT LPAREN parameter_list RPAREN module_body",
        "XMV_MODULE IDENT module_body"
    )
    def module(self, p):
        if len(p) == 3:
            return XMVModule(name=p[1], parameters=[], elements=p[2])
        else:
            return XMVModule(name=p[1], parameters=p[3], elements=p[5])
    

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
        "XMV_LTLSPEC ltl_expr",
        "XMV_LTLSPEC ltl_expr SEMICOLON"
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
                return XMVInvarspecDeclaration(formula=p[1])
            case "LTLSPEC":
                return XMVLtlspecDeclaration(formula=p[1])
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
            "expr AMPERSAND expr",
            "expr BAR expr",
            "expr XMV_XOR expr",
            "expr XMV_XNOR expr",
            "expr RIGHTARROW expr",
            "expr LEFTRIGHTARROW expr",
            "expr EQUAL expr",
            "expr NOTEQUAL expr",
            "expr LESSTHAN expr",
            "expr GREATERTHAN expr",
            "expr LESSEQUAL expr",
            "expr GREATEREQUAL expr",
            "expr PLUS expr",
            "expr MINUS expr",
            "expr STAR expr",
            "expr DIVIDE expr",
            "expr XMV_MOD expr",
            "expr LSHIFT expr",
            "expr RSHIFT expr",
            "expr XMV_UNION expr",
            "expr XMV_IN expr",
            "IDENT LPAREN cs_expr_list RPAREN"
    )
    def expr(self, p):
        if len(p) == 1: # TODO: constants/whatever
            return p[0]
        if len(p) == 2: # unop
            return XMVUnop(op=p[0], arg=p[1])
        if len(p) == 3: # binop
            return XMVBinop(op=p[1], lhs=p[0], rhs=p[2]) 
        if len(p) == 4: # function call
            return XMVFuncall(function_name=p[0], function_args=p.cs_expr_list)
        
    @_("NEXT LPAREN expr RPAREN")
    def expr(self, p):
        return XMVFuncall(function_name="next", function_args=[p[2]])
    
    @_("XMV_SIGNED LPAREN expr RPAREN")
    def expr(self, p):
        return XMVFuncall(function_name="signed", function_args=[p[2]])


    @_("expr LBRACK INTEGER RBRACK")
    def expr(self, p):
        return XMVIndexSubscript(array=p.expr, index=int(p[2]))

    @_("expr LBRACK INTEGER COLON INTEGER RBRACK")
    def expr(self, p):
        return XMVWordBitSelection(word=p.expr, low=int(p[2]), high=int(p[4]))

    @_("expr CONCAT expr")
    def expr(self, p):
        return XMVBinop(op="concat", lhs=p[0], rhs=p[2])
    
    @_("LBRACE cs_expr_list RBRACE")
    def expr(self, p):
        return XMVSetBodyExpression(members=p.cs_expr_list)
    
    @_("expr QUESTIONMARK expr COLON expr")
    def expr(self, p):
        return XMVTernary(cond=p[0], then_expr=p[2], else_expr=p[4])
    
    @_("case_expr")
    def expr(self, p):
        return p[0]
    
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

    # @_("complex_identifier DOT IDENT")
    # def complex_identifier(self, p):
    #     return XMVModuleAccess(p[0], p[2])


    @_("IDENT")
    def complex_identifier(self, p):
        return XMVIdentifier(p[0])
    
    # type specifier rules

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
            "IDENT LPAREN parameter_list RPAREN"
    )
    def type_specifier(self, p):
        match p[0]:
            case "boolean":
                return XMVBoolean()
            case "integer":
                return XMVInteger()
            case "word":
                return XMVWord(width=p[2], signed=False)
            case "unsigned":
                return XMVWord(width=p[3], signed=False)
            case "signed":
                return XMVWord(width=p[3], signed=True)
            case "real":
                return XMVReal()
            case "clock":
                return XMVClock()
            case "{":
                return XMVEnumeration(summands=p[1])
            case "array":
                return XMVArray(low=p[2], high=p[5], type=p[7])
            case _:
                if str.isnumeric(p[0]):
                    return XMVRange(low=p[0], high=p[3])
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
        
    @_(
            "IDENT",
            "INTEGER"
    )
    def enumeration_type_value(self, p):
        return p[0]
    
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
    
    @_("EXCLAMATION ltl_expr")
    def ltl_expr(self, p):
        return XMVLTLLogUnop(op="!", arg=p.ltl_expr)
    
    @_(
        "ltl_expr AMPERSAND ltl_expr",
        "ltl_expr BAR ltl_expr",
        "ltl_expr XMV_XOR ltl_expr",
        "ltl_expr XMV_XNOR ltl_expr",
        "ltl_expr RIGHTARROW ltl_expr",
        "ltl_expr LEFTRIGHTARROW ltl_expr"
    )
    def ltl_expr(self, p):
        return XMVLTLLogBinop(op=p[1], lhs=p[0], rhs=p[2])
    
    
    @_("constant")
    def ltl_expr(self, p):
        return p[0]
    
    @_("NEXT LPAREN expr RPAREN")
    def ltl_expr(self, p):
        return XMVFuncall(function_name="next", function_args=p.expr)

    

    @_("LTLUNOP ltl_expr")
    def ltl_expr(self, p):
        return XMVLTLUnop(op=p[0], arg=p[1])
    
    @_("ltl_expr LTLBINOP ltl_expr")
    def ltl_expr(self, p):
        return XMVLTLBinop(op=p[1], lhs=p[0], rhs=p[2])
    
    @_("complex_identifier", "LPAREN ltl_expr RPAREN")
    def ltl_expr(self, p):
        if len(p) == 1:
            return p[0]
        else:
            return p.ltl_expr

def main():
    argparser = argparse.ArgumentParser(
        prog='nuXmv/NuSMV parser',
        description='Parses a nuXmv/NuSMV (.smv) file into an AST defined in xmv.py'
   )

    argparser.add_argument('filename')
    args = argparser.parse_args()
    file = open(args.filename)

    lexer = NuXmvLexer()
    parser = NuXmvParser()

    file_string = file.read()
    # for tok in lexer.tokenize(file_string):
    #         print(f"type:{tok.type}, value:{tok.value}")

    result = parser.parse(lexer.tokenize(file_string))

    # print(result)
    return


if __name__ == '__main__':
    main()