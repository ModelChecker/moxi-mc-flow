%{

/*
This software has been determined to be outside the scope of NASA NPG 2210 and
therefore is not considered as controlled software.

This program may be freely redistributed and/or modified under the terms of
this software agreement.

NASA is neither liable nor responsible for maintenance, updating, or
correction of any errors in the software provided.

Use of this software shall not be construed to constitute the grant of a
license to the user under any NASA patent, patent application or other
intellectual property.

THE SOFTWARE IS PROVIDED 'AS IS' WITHOUT ANY WARRANTY OF ANY KIND, EITHER
EXPRESSED, IMPLIED, OR STATUTORY, INCLUDING, BUT NOT LIMITED TO, ANY WARRANTY
THAT THE SOFTWARE WILL CONFORM TO SPECIFICATIONS, ANY IMPLIED WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE, AND FREEDOM FROM
INFRINGEMENT, AND ANY WARRANTY THAT THE DOCUMENTATION WILL CONFORM TO THE
SOFTWARE, OR ANY WARRANTY THAT THE SOFTWARE WILL BE ERROR FREE.  IN NO EVENT
SHALL NASA BE LIABLE FOR ANY DAMAGES, INCLUDING, BUT NOT LIMITED TO, DIRECT,
INDIRECT, SPECIAL OR CONSEQUENTIAL DAMAGES, ARISING OUT OF, RESULTING FROM, OR
IN ANY WAY CONNECTED WITH THIS SOFTWARE, WHETHER OR NOT BASED UPON WARRANTY,
CONTRACT, TORT , OR OTHERWISE, WHETHER OR NOT INJURY WAS SUSTAINED BY PERSONS
OR PROPERTY OR OTHERWISE, AND WHETHER OR NOT LOSS WAS SUSTAINED FROM, OR AROSE
OUT OF THE RESULTS OF, OR USE OF, THE SOFTWARE OR SERVICES PROVIDED
HEREUNDER.
 
RECIPIENT AGREES TO WAIVE ANY AND ALL CLAIMS AGAINST THE U.S. GOVERNMENT, THE
U.S. GOVERNMENT'S CONTRACTORS AND SUBCONTRACTORS, AND SHALL INDEMNIFY AND HOLD
HARMLESS THE U.S. GOVERNMENT AND THE U.S. GOVERNMENT'S CONTRACTORS AND
SUBCONTRACTORS FOR ANY DAMAGE THAT MAY BE INCURRED FROM RECIPIENT'S PRIOR OR
FUTURE USE OF THE PROVIDED SOFTWARE, INCLUDING ANY DAMAGES FROM PRODUCTS BASED
ON, OR RESULTING FROM, THE USE THEREOF.  RECIPIENT AGREES TO OBTAIN THIS
IDENTICAL WAIVER OF CLAIMS, INDEMNIFICATION AND HOLD HARMLESS AGREEMENT WITH
ANY ENTITIES THAT ARE PROVIDED WITH TECHNICAL DATA DERIVED FROM USE OF THE
SOFTWARE.

K.Y.Rozier
June, 2011
*/

/* This is a lexer for LTL formulas in in-fix order */
#include "y.tab.h"
#include <string.h>

extern "C" int yylex();

%}
%%
[\t ]+       /*ignore whitespace*/ ;

&&        { 
  /*ECHO; /* normal default anyway */ 
    fprintf(stderr, "ERROR: Unrecognized symbol: %s\nTry &\n", yytext);
    exit(1);
}
&  { 
    /*fprintf(stderr, "%s is a logical operator\n", yytext);*/
    return AND;
   }
\|\|        { 
  /*ECHO; /* normal default anyway */ 
    fprintf(stderr, "ERROR: Unrecognized symbol: %s\nTry |\n", yytext);
    exit(1);
}
\| { 
    /*fprintf(stderr, "%s is a logical operator\n", yytext);*/
    return OR;
   }

~  { 
    /*fprintf(stderr, "%s is a logical operator\n", yytext);*/
    return NOT;
   }
-> { 
    /*fprintf(stderr, "%s is a logical operator\n", yytext);*/
    return IMPLIES;
   }

X  { 
    /*fprintf(stderr, "%s is a temporal operator\n", yytext);*/
    return NEXT;
   }
U  { 
    /*fprintf(stderr, "%s is a temporal operator\n", yytext);*/
    return UNTIL;
   }
R  { 
    /*fprintf(stderr, "%s is a temporal operator\n", yytext);*/
    return RELEASE;
   }
G  { 
    /*fprintf(stderr, "%s is a temporal operator\n", yytext);*/
    return GLOBALLY;
   }
F  { 
    /*fprintf(stderr, "%s is a temporal operator\n", yytext);*/
    return FUTURE;
   }

FALSE  { 
    /*fprintf(stderr, "%s is a boolean truth value\n", yytext);*/
    return FFALSE;
   }

TRUE  { 
  /*fprintf(stderr, "%s is a boolean truth value\n", yytext);*/
    return TTRUE;
   }

[a-zA-Z_0-9]+   { 
  /*fprintf(stderr, "%s is a variable\n", yytext);*/
  yylval.varName = (char *)malloc((strlen(yytext)+1)*sizeof(char));
  if (yylval.varName==NULL){ fprintf(stderr, "Memory error24\n"); exit(1); }
  /*copy in the variable name*/
  strcpy(yylval.varName, yytext);
  /*fprintf(stderr, "saved variable %s\n", yylval.varName);
    fprintf(stderr, "returning PROP\n");*/
  return PROP;
}

\( {
  /*fprintf(stderr, "Got '('\n");*/
  return LPAREN;
}

\) {
  /*fprintf(stderr, "Got ')'\n");*/
    return RPAREN;
  }

\n { /*This signifies the end of input*/ 
    return 0;}

.        { 
    ECHO; /* normal default anyway */ 
    fprintf(stderr, "ERROR: Unrecognized symbol: %s\n", yytext);
    exit(1);
}
%%

/*int main(void) {
    yylex();

    return 0;
} /*end main*/
