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

/* This is a parser for LTL formulas in in-fix order */

#include "PANDA.h"

extern "C" int yylex();

// int yylex(); /*to make g++ shut up*/

int yyerror(const char *msg) { /*to make g++ shut up*/
    (void) fprintf(stderr, "%s\n", msg);
    return (0);
} /*end yyerror*/

/*Variable declarations*/   
 struct node *current;
 int i;

 KItem search;            /*a variable name to search for*/
 int used;                /*did we use this var already?*/


/*for parsing the formula string*/
#undef YY_INPUT
#define YY_INPUT(b, r, ms) (r = my_yyinput(b, me))

%}

%union {
    struct node *nPtr;		/* node pointer */
    char *varName;              /* name of a variable */
};

%token AND OR NOT IMPLIES NEXT UNTIL GLOBALLY LPAREN RPAREN
%token <varName> PROP 
%token FFALSE TTRUE

/* Establish precedence rules and left-associativity*/
/* (different from SMV -- I think ~ should bind tighter than U) */
%left RELEASE      /*  release  */
%left UNTIL        /*   until   */
%left IMPLIES      /*     ->    */
%left OR           /*     or    */
%left AND          /*    and    */
%nonassoc GLOBALLY /*    globally   */
%nonassoc FUTURE   /* in the future */
%nonassoc NEXT     /*   next time   */
%nonassoc NOT      /*      not      */
%nonassoc PROP
%nonassoc TTRUE
%nonassoc FFALSE

%type <nPtr> input formula

%%
input: formula { /*a simple top-level to assign the root*/
    root = $1;
    /*fprintf(stderr, "Finished parsing formula\n");*/
}
;

formula: 
PROP { 
    /*printf("Found a leaf\n"); */
    numPROP++; /*count it*/
    current = (struct node *)malloc(sizeof(struct node));
    if (current==NULL){ fprintf(stderr, "Memory error11\n"); exit(1); }
    current->me = (char *)malloc((strlen(yylval.varName)+1)*sizeof(char));
    if (current->me==NULL){ fprintf(stderr, "Memory error25\n"); exit(1); }
    strcpy(current->me, yylval.varName); /*copy in the operator*/
    /*fprintf(stderr, "1 saving %s\n", current->me);*/
    current->left_kid = NULL;
    current->right_kid = NULL;
    current->temp_kid = 0; /*no temporal children*/
    $$ = current;
    formula_length += strlen(yylval.varName)+3;
    /*fprintf(stderr, "Found a proposition (%s) of length %d\n", yylval.varName, strlen(yylval.varName));*/

    /*Check if we've declared this variable yet*/
    search.setName(current->me);
    used = varList.query(search);
    if (used == 0) { /*we haven't used this variable name yet*/
	/*Add the var to the list so we don't use it again*/
	//current->num = 
	varList.addItem(search);
	/*Make self-loops at all vertices in the variable graph*/
	/*connect_graph(current->num, current->num);*/
    } /*end if*/
    current->num = -1;
    /*printf("Parsed a simple subformula.\n"); */
}
| TTRUE { 
    /*printf("Found a TRUE\n"); */
    numTRUE++; /*count it*/
    current = (struct node *)malloc(sizeof(struct node));
    if (current==NULL){ fprintf(stderr, "Memory error11\n"); exit(1); }
    current->me = (char *)malloc(6*sizeof(char));
    if (current->me==NULL){ fprintf(stderr, "Memory error25\n"); exit(1); }
    strcpy(current->me, "TRUE"); /*copy in the operator*/
    /*fprintf(stderr, "1 saving %s\n", current->me);*/
    current->left_kid = NULL;
    current->right_kid = NULL;
    current->temp_kid = 0; /*no temporal children*/
    $$ = current;
    formula_length += 6;
    /*printf("Found a TRUE\n");*/
    /*printf("Parsed a simple subformula.\n"); */
}
| FFALSE { 
  /*fprintf(stderr, "Found a FALSE\n");*/
    numFALSE++; /*count it*/
    current = (struct node *)malloc(sizeof(struct node));
    if (current==NULL){ fprintf(stderr, "Memory error11\n"); exit(1); }
    current->me = (char *)malloc(7*sizeof(char));
    if (current->me==NULL){ fprintf(stderr, "Memory error25\n"); exit(1); }
    strcpy(current->me, "FALSE"); /*copy in the operator*/
    /*fprintf(stderr, "1 saving %s\n", current->me);*/
    current->left_kid = NULL;
    current->right_kid = NULL;
    current->temp_kid = 0; /*no temporal children*/
    $$ = current;
    formula_length += 7;
    /*printf("Parsed a simple subformula.\n"); */
}
| NOT formula {
    /*printf("Found a '~' operator\n"); */
    /*numNonTemporalOps++; /*DON'T count it: NOT's are dispensible*/
    current = (struct node *)malloc(sizeof(struct node));
    if (current==NULL){ fprintf(stderr, "Memory error11\n"); exit(1); }
    current->me = (char *)malloc(2*sizeof(char));
    if (current->me==NULL){ fprintf(stderr, "Memory error12\n"); exit(1); }
    current->me[0] = '~'; /*copy in the operator*/
    current->me[1] = '\0'; /*end the string*/
    /*fprintf(stderr, "Saving %s\n", current->me);*/
    current->num = -1;
    current->left_kid = NULL;
    current->right_kid = $2;
    current->right_kid->parent = current;
    if ((current->right_kid->me[0] == 'X')
	|| (current->right_kid->me[0] == 'U')
	|| (current->right_kid->me[0] == 'R')
	|| (current->right_kid->me[0] == 'F')
	|| (current->right_kid->me[0] == 'G')) {
	current->temp_kid = 1;
    } /*end if*/
    else {
	current->temp_kid = 0; /*no temporal children*/
    } /*end else*/
    $$ = current;
    formula_length += 3;
    /*printf("Done with '~' operator\n");*/
}
| NEXT formula { 
    /*printf("Found a 'X' operator\n"); */
    numX++; /*count it*/
    current = (struct node *)malloc(sizeof(struct node));
    if (current==NULL){ fprintf(stderr, "Memory error11\n"); exit(1); }
    current->me = (char *)malloc(2*sizeof(char));
    if (current->me==NULL){ fprintf(stderr, "Memory error12\n"); exit(1); }
    current->me[0] = 'X'; /*copy in the operator*/
    current->me[1] = '\0'; /*end the string*/
    /*fprintf(stderr, "Saving %s\n", current->me);*/
    current->num = -1;
    current->left_kid = NULL;
    current->right_kid = $2;
    current->right_kid->parent = current;
    if ((current->right_kid->me[0] == 'X')
	|| (current->right_kid->me[0] == 'U')
	|| (current->right_kid->me[0] == 'R')
	|| (current->right_kid->me[0] == 'F')
	|| (current->right_kid->me[0] == 'G')) {
	current->temp_kid = 1;
    } /*end if*/
    else {
	current->temp_kid = 0; /*no temporal children*/
    } /*end else*/
    $$ = current;
    formula_length += 3;
    /*printf("Done with 'X' operator\n");*/
}
| GLOBALLY formula {
    /*printf("Found a 'G' operator\n"); */
    numG++; /*count it*/
    current = (struct node *)malloc(sizeof(struct node));
    if (current==NULL){ fprintf(stderr, "Memory error11\n"); exit(1); }
    current->me = (char *)malloc(2*sizeof(char));
    if (current->me==NULL){ fprintf(stderr, "Memory error12\n"); exit(1); }
    current->me[0] = 'G'; /*copy in the operator*/
    current->me[1] = '\0'; /*end the string*/
    /*fprintf(stderr, "Saving %s\n", current->me);*/
    current->num = -1;
    current->left_kid = NULL;
    current->right_kid = $2;
    current->right_kid->parent = current;
    if ((current->right_kid->me[0] == 'X')
	|| (current->right_kid->me[0] == 'U')
	|| (current->right_kid->me[0] == 'R')
	|| (current->right_kid->me[0] == 'F')
	|| (current->right_kid->me[0] == 'G')) {
	current->temp_kid = 1;
    } /*end if*/
    else {
	current->temp_kid = 0; /*no temporal children*/
    } /*end else*/
    if (current->right_kid->me[0] == 'F') {
	numGF++; /*count this special operator*/
    } /*end if*/
    $$ = current;
    formula_length += 3;
    /*printf("Done with 'G' operator\n");*/
} 
| FUTURE formula {
    /*printf("Found an 'F' operator\n"); */
    numF++; /*count it*/
    current = (struct node *)malloc(sizeof(struct node));
    if (current==NULL){ fprintf(stderr, "Memory error11\n"); exit(1); }
    current->me = (char *)malloc(2*sizeof(char));
    if (current->me==NULL){ fprintf(stderr, "Memory error12\n"); exit(1); }
    current->me[0] = 'F'; /*copy in the operator*/
    current->me[1] = '\0'; /*end the string*/
    /*fprintf(stderr, "Saving %s\n", current->me);*/
    current->num = -1;
    current->left_kid = NULL;
    current->right_kid = $2;
    current->right_kid->parent = current;
    if ((current->right_kid->me[0] == 'X')
	|| (current->right_kid->me[0] == 'U')
	|| (current->right_kid->me[0] == 'R')
	|| (current->right_kid->me[0] == 'F')
	|| (current->right_kid->me[0] == 'G')) {
	current->temp_kid = 1;
    } /*end if*/
    else {
	current->temp_kid = 0; /*no temporal children*/
    } /*end else*/
    $$ = current;
    formula_length += 3;
    /*printf("Done with 'F' operator\n");*/
} 
| formula AND formula {
    /*printf("Found a '&' operator\n"); */
    numNonTemporalOps++; /*count it*/
    current = (struct node *)malloc(sizeof(struct node));
    if (current==NULL){ fprintf(stderr, "Memory error11\n"); exit(1); }
    current->me = (char *)malloc(2*sizeof(char));
    if (current->me==NULL){ fprintf(stderr, "Memory error12\n"); exit(1); }
    current->me[0] = '&'; /*copy in the operator*/
    current->me[1] = '\0'; /*end the string*/
    /*fprintf(stderr, "Saving %s\n", current->me);*/
    current->num = -1;
    current->left_kid = $1;
    current->right_kid = $3;
    current->left_kid->parent = current;
    current->right_kid->parent = current;
    if ((current->right_kid->me[0] == 'X')    || (current->left_kid->me[0] == 'X')
	|| (current->right_kid->me[0] == 'U') || (current->left_kid->me[0] == 'U')
	|| (current->right_kid->me[0] == 'R') || (current->left_kid->me[0] == 'R')
	|| (current->right_kid->me[0] == 'F') || (current->left_kid->me[0] == 'F')
	|| (current->right_kid->me[0] == 'G') || (current->left_kid->me[0] == 'G')) {
	current->temp_kid = 1;
    } /*end if*/
    else {
	current->temp_kid = 0; /*no temporal children*/
    } /*end else*/
    $$ = current;
    formula_length += 3;
    /*printf("Done with '&' operator\n");*/
}
| formula OR formula {
    /*fprintf(stderr, "Found a '|' operator\n"); */
    numNonTemporalOps++; /*count it*/
    current = (struct node *)malloc(sizeof(struct node));
    if (current==NULL){ fprintf(stderr, "Memory error11\n"); exit(1); }
    current->me = (char *)malloc(2*sizeof(char));
    if (current->me==NULL){ fprintf(stderr, "Memory error12\n"); exit(1); }
    current->me[0] = '|'; /*copy in the operator*/
    current->me[1] = '\0'; /*end the string*/
    /*fprintf(stderr, "Saving %s\n", current->me);*/
    current->num = -1;
    current->left_kid = $1;
    current->right_kid = $3;
    current->left_kid->parent = current;
    current->right_kid->parent = current;
    if ((current->right_kid->me[0] == 'X')    || (current->left_kid->me[0] == 'X')
	|| (current->right_kid->me[0] == 'U') || (current->left_kid->me[0] == 'U')
	|| (current->right_kid->me[0] == 'R') || (current->left_kid->me[0] == 'R')
	|| (current->right_kid->me[0] == 'F') || (current->left_kid->me[0] == 'F')
	|| (current->right_kid->me[0] == 'G') || (current->left_kid->me[0] == 'G')) {
	current->temp_kid = 1;
    } /*end if*/
    else {
	current->temp_kid = 0; /*no temporal children*/
    } /*end else*/
    $$ = current;
    formula_length += 3;
    /*printf("Done with '|' operator\n");*/
}
| formula IMPLIES formula {
    /*printf("Found a '->' operator\n"); */
    numNonTemporalOps++; /*count it: maybe count twice for now since it's ~|? */
    current = (struct node *)malloc(sizeof(struct node));
    if (current==NULL){ fprintf(stderr, "Memory error11\n"); exit(1); }
    current->me = (char *)malloc(2*sizeof(char));
    if (current->me==NULL){ fprintf(stderr, "Memory error12\n"); exit(1); }
    current->me[0] = '-'; /*copy in the operator*/
    current->me[1] = '\0'; /*end the string*/
    /*fprintf(stderr, "Saving %s\n", current->me);*/
    current->num = -1;
    current->left_kid = $1;
    current->right_kid = $3;
    current->left_kid->parent = current;
    current->right_kid->parent = current;
    if ((current->right_kid->me[0] == 'X')    || (current->left_kid->me[0] == 'X')
	|| (current->right_kid->me[0] == 'U') || (current->left_kid->me[0] == 'U')
	|| (current->right_kid->me[0] == 'R') || (current->left_kid->me[0] == 'R')
	|| (current->right_kid->me[0] == 'F') || (current->left_kid->me[0] == 'F')
	|| (current->right_kid->me[0] == 'G') || (current->left_kid->me[0] == 'G')) {
	current->temp_kid = 1;
    } /*end if*/
    else {
	current->temp_kid = 0; /*no temporal children*/
    } /*end else*/
    $$ = current;
    formula_length += 4;
    /*printf("Done with '->' operator\n");*/
}
| formula UNTIL formula {
    /*printf("Found a 'U' operator\n"); */
    numU++; /*count it*/
    /*fprintf(stderr, "Found a U!\n");*/
    current = (struct node *)malloc(sizeof(struct node));
    if (current==NULL){ fprintf(stderr, "Memory error11\n"); exit(1); }
    current->me = (char *)malloc(2*sizeof(char));
    if (current->me==NULL){ fprintf(stderr, "Memory error12\n"); exit(1); }
    current->me[0] = 'U'; /*copy in the operator*/
    current->me[1] = '\0'; /*end the string*/
    /*fprintf(stderr, "Saving %s\n", current->me);*/
    current->num = -1;
    current->left_kid = $1;
    current->right_kid = $3;
    current->left_kid->parent = current;
    current->right_kid->parent = current;
    if ((current->right_kid->me[0] == 'X')    || (current->left_kid->me[0] == 'X')
	|| (current->right_kid->me[0] == 'U') || (current->left_kid->me[0] == 'U')
	|| (current->right_kid->me[0] == 'R') || (current->left_kid->me[0] == 'R')
	|| (current->right_kid->me[0] == 'F') || (current->left_kid->me[0] == 'F')
	|| (current->right_kid->me[0] == 'G') || (current->left_kid->me[0] == 'G')) {
	current->temp_kid = 1;
    } /*end if*/
    else {
	current->temp_kid = 0; /*no temporal children*/
    } /*end else*/
    $$ = current;
    formula_length += 3;
    /*printf("Done with 'U' operator\n");*/
}
| formula RELEASE formula {
    /*printf("Found an 'R' operator\n"); */
    numR++; /*count it*/
    current = (struct node *)malloc(sizeof(struct node));
    if (current==NULL){ fprintf(stderr, "Memory error11\n"); exit(1); }
    current->me = (char *)malloc(2*sizeof(char));
    if (current->me==NULL){ fprintf(stderr, "Memory error12\n"); exit(1); }
    current->me[0] = 'R'; /*copy in the operator*/
    current->me[1] = '\0'; /*end the string*/
    /*fprintf(stderr, "Saving %s\n", current->me);*/
    current->num = -1;
    current->left_kid = $1;
    current->right_kid = $3;
    current->left_kid->parent = current;
    current->right_kid->parent = current;
    if ((current->right_kid->me[0] == 'X')    || (current->left_kid->me[0] == 'X')
	|| (current->right_kid->me[0] == 'U') || (current->left_kid->me[0] == 'U')
	|| (current->right_kid->me[0] == 'R') || (current->left_kid->me[0] == 'R')
	|| (current->right_kid->me[0] == 'F') || (current->left_kid->me[0] == 'F')
	|| (current->right_kid->me[0] == 'G') || (current->left_kid->me[0] == 'G')) {
	current->temp_kid = 1;
    } /*end if*/
    else {
	current->temp_kid = 0; /*no temporal children*/
    } /*end else*/
    $$ = current;
    formula_length += 3;
    /*printf("Done with 'R' operator\n");*/
}
| LPAREN formula RPAREN { 
    /*printf("Found parens!\n"); */
    $$ = $2;
    formula_length += 2;
}
;

%%

/*node * main(void) {
    return yyparse();
} /*end main*/

