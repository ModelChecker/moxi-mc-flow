/* PANDA.cpp

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
*/

/* PANDA.cpp

   Kristin Y. Rozier
   released: June, 2011

   Input: an LTL formula

   Output: a symbolic automaton model of the input formula (for NuSMV, Cadence SMV, or SAL)
           OR (with -pnnf) just the negation normal form of the formula
           OR (with -pbnf) just the boolean normal form of the formula
	   OR (with -pnor) just the formula with all R-operators replaced by ~(~aU~b) constructions
*/

/*NOTE: For this parser, formulas MUST be enclosed within parens!*/

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <ctype.h>
#include "PANDA.h"

#define flagBufLength 10


/*Global Variables*/
struct node *root;       /*the root of the parse tree*/
size_t formula_length;   /*the length of the input formula*/
FILE *OUT;               /*SMV output file*/
FILE *SOUT;              /*outfile to store the S_h characteristic function definition*/
FILE *TOUT;              /*outfile to store the TRANS statements*/
FILE *FOUT;              /*outfile to store the CTL fairness assertions*/
FILE *VOUT;              /*SMV variable order file*/
int Xcounter = 0;
KList varList;           /*list of used variables to avoid repeats*/
KList funcList;          /*list of characteristic function definitions to avoid repeats*/
graph_t var_graph;       /*rgl2-library style variable graph*/
int *order_array;        /*array of var numbers returned from rgl2*/

/*Operator Counters*/
int numNonTemporalOps = 0; /*how many &'s, |'s, and ->'s are in the input formula?*/
int numX  = 0;           /*how many X's are in the input formula?*/
int numU  = 0;           /*how many U's are in the input formula?*/
int numR  = 0;           /*how many R's are in the input formula?*/
int numG  = 0;           /*how many G's are in the input formula?*/
int numGF = 0;           /*how many GF's are in the input formula? (These also get counted individually.)*/
int numF  = 0;           /*how many F's are in the input formula?*/
int numPROP = 0;         /*how many times are props used in the input formula?*/
int numTRUE = 0;         /*how many times is TRUE used in the input formula?*/
int numFALSE = 0;         /*how many times is FALSE used in the input formula?*/

/*flags*/
short verbose = 0;       /*1 for verbose; 0 otherwise is the default*/
char  smvFlag;           /*n for NuSMV or c for CadenceSMV -- designates comment style*/
                         /*s for SAL -- more differences from the SMV's than comments*/
short printBNF = 0;      /*1 for print boolean normal form only; 0 otherwise is the default*/
short printNNF = 0;      /*1 for print negation normal form only; 0 otherwise is the default*/
short printNoR = 0;      /*1 for print formula with no R-operators only; 0 otherwise is the default*/
short useNNF = 0;        /*convert all formulas into NNF; default is to use boolean normal form*/
short sloppy = 0;        /*use sloppy encoding; default is to use fussy*/
short nextOpPresent = 0; /*1 if a X operator is in the formula; needed for model construction*/
int   fairnum = 0;       /*number of fairness statements; used for naming them in SAL and avoiding errors in SMV's*/
char  varOrder = 'z';    /*m for MCS, x for LEXM, p for LEXP, l for Linear*/
short reverseOrder = 0;  /*1 if chosen varOrder is to be reversed*/
mcs_start_t mcs_start_node = MAX;    /* Either MIN, MAX, ZERO, or RANDOM*/
short tgba = 0;          /*form a transition-based symbolic automaton instead of the default state-based one*/
short define_P_vars = 0; /*put a TRANS statement for each promise var?*/

/*Function negate:
    Negate the given node in the parse tree.

Input: a pointer to the node in the parse tree to be negated.
*/
void negate(struct node *current) {
    struct node *previous;

    if(current == NULL) {
	fprintf(stderr, "Warning: Can't negate an empty operator!\n");
	return;
    } /*end if*/

    if (verbose) {
	fprintf(stderr, "Negating operator %s...\n", current->me);
	if (root -> parent != NULL) {
	    fprintf(stderr, "ERROR: root->parent != NULL\n");
	} /*end if*/
    } /*end if*/

    if (current->parent != NULL) {
	previous = current->parent;
	if (previous->left_kid == current) {
	    previous->left_kid = (struct node *)malloc(sizeof(struct node));
	    if (previous->left_kid == NULL){ fprintf(stderr, "Memory error5\n"); 
	    exit(1); }
	    previous->left_kid->parent = previous;
	    previous = previous->left_kid;
	} /*end if*/
	else if (previous->right_kid == current) {
	    previous->right_kid = (struct node *)malloc(sizeof(struct node));
	    if (previous->right_kid == NULL){ fprintf(stderr, "Memory error6\n");
	    exit(1); }
	    previous->right_kid->parent = previous;
	    previous = previous->right_kid;
	} /*end else if*/
	else {
	    fprintf(stderr, "ERROR: disjoint parse tree! Exiting...\n");
	    exit(1);
	} /*end else*/
    } /*end if*/
    else { /*dealing with the root!*/
	if (current != root) {
	    fprintf(stderr, "ERROR: disjoint parse tree! Exiting...\n");
	    exit(1);
	} /*end if*/
	previous = (struct node *)malloc(sizeof(struct node));
	if (previous == NULL){ fprintf(stderr, "Memory error7\n"); exit(1); }
	root = previous;
	previous->parent = NULL;
    } /*end else*/
    previous->me = (char *)malloc(2*sizeof(char));
    if (previous->me == NULL){ fprintf(stderr, "Memory error8\n"); exit(1); }
    previous->me[0] = '~'; /*copy in the operator*/
    previous->me[1] = '\0'; /*end the string*/
    previous->left_kid = NULL;
    previous->right_kid = current;
    current->parent = previous;
    previous->num = -1;
    if ((current->me[0] == 'X')
	|| (current->me[0] == 'U')
	|| (current->me[0] == 'R')
	|| (current->me[0] == 'F')
	|| (current->me[0] == 'G')) {
	previous->temp_kid = 1;
    } /*end if*/
    else {
	previous->temp_kid = 0; /*no temporal children*/
    } /*end else*/

    formula_length += 3; /*a becomes (~ a)*/

    return;
} /*end negate*/


/*Function to print the parse tree*/
void printTree(struct node *my_root) {

    struct node *current = my_root;
    char *formula;
    int i = 0;
    int level = 0;       /*current level*/
    int print_level = 0; /*level we are currently printing*/
    short visited_left=0, visited_right=0;
    short still_printing = 1; /*did we print anything at the last level? 
			       (or have we exhausted the tree?)*/

    /*Error Check*/
    if(current == NULL) {
	fprintf(stderr, "Warning: Can't print an empty formula\n");
	return;
    } /*end if*/

    if (verbose) {
	fprintf(stderr, "---------------------------\nprintTree root is %s\n", my_root->me);
    } /*end if*/

    /*print header*/
    fprintf(stderr, "Level(L->R)\tMe\tVarNum\tTemp kid?\n");

    level = 0; 
    print_level = 0; 
    still_printing = 1;
    while (still_printing == 1) {
	still_printing = 0; /*reset for this level*/
	visited_left = 0;   /*reset for this level*/
	visited_right = 0;  /*reset for this level*/

	/*Loop while we haven't reached the root 
	  after exploring it's right branch*/
	while (! ((current == root) && (visited_right == 1)) ) {
	    
	    if (level == print_level) {
		visited_left = 1;
	    } /*end if*/

	    if (visited_left == 1) {
		visited_left = 0;
	    } /*end if*/
	    else {
		if ((level < print_level) /*if we need to go down more*/ 
		    && (current->left_kid != NULL)) {
		    current = current->left_kid;
		    level++; /*increase the level: we're going down*/
		    continue;
		} /*end if*/
	    } /*end else*/
	    
	    if (visited_right == 1) {
		visited_right = 0;
	    } /*end if*/
	    else {
		if (level == print_level) {
		    /*Print this node*/
		    fprintf(stderr, "%d\t\t%s\t%d\t%d\n", level, current->me, current->num, current->temp_kid);
		    still_printing = 1; /*we did successfully print at this level*/
		    visited_right = 1;
		} /*end if*/
		
		if ((level < print_level) /*if we need to go down more*/ 
		    && (current->right_kid != NULL)) {
		    current = current->right_kid;
		    level++; /*increase the level: we're going down*/
		    continue;
		} /*end if*/
	    } /*end else*/
	    
	    if (current->parent != NULL) {
		visited_left = 1;
		level--; /*decrease the level: we're going up*/
		if (current->parent->right_kid == current) {
		    visited_right = 1;
		} /*end if*/
		else {visited_right = 0;} /*just added*/
		current = current->parent;
	    } /*end if*/
	    
	    i++;
	} /*end while*/	
	print_level++; /*increase the level for next time*/
    } /*end while*/

    return;
    
} /*end printTree*/


/*Purpose:
  - add a connection in the rgl2 var_graph
  - increment the appropriate node's outDegree in the varList
*/
void connect_graph(int from, int to) {
  
    string fromVar; /*string var name of "from" variable*/
    string toVar;   /*string var name of "to" variable*/

    /*Error checking*/
    if ( (from == -1) || (to == -1) ) {
	fprintf(stderr, "ERROR: can't connect an invalid variable id. From = %d; To = %d. Exiting...\n", from, to);
	exit(1);
    } /*end if*/

    /*prevent redundancy*/
    if (has_edge_graph(var_graph, from, to)) { /*this is an rgl2 function*/
	return; /*the edge already exists*/
    } /*end if*/

    if (verbose) {
	//fprintf(stderr, "from = %d; to = %d\n", from, to);
	fprintf(stderr, "connecting from %s (var %d) to %s (var %d)\n", varList.findName(from).c_str(), from, varList.findName(to).c_str(), to);
    } /*end if*/

    connect_graph(var_graph, from, to); /*this is an rgl2 function*/

    /*increase the out degrees of both verticies since this is an undirected graph*/
    fromVar = varList.findName(from);
    toVar = varList.findName(to);
    KItem f = varList.find(fromVar);
    KItem t = varList.find(toVar);
    int fdeg = f.getOutDegree() + 1;
    int tdeg = t.getOutDegree() + 1;
    f.setOutDegree(fdeg);
    t.setOutDegree(tdeg);
    varList.saveItem(f); 
    varList.saveItem(t); 
    if (verbose == 1) {
	fprintf(stderr, "Connecting %d to %d: outDegrees = %d, %d\n", from, to, varList.findItemByNumber(from).getOutDegree(), varList.findItemByNumber(to).getOutDegree());
    } /*end if*/

} /*end connect_graph*/


void printFormula(size_t formula_length) {
    struct node *current = root;
    char *formula;
    int i = 0;
    short visited_left=0, visited_right=0;

    /*Error Check*/
    if((formula_length == 0) || (current == NULL)) {
	fprintf(stderr, "Warning: Can't print an empty formula\n");
	return;
    } /*end if*/

    formula = (char *)malloc(sizeof(char) * ((formula_length*2)+1));
    if (formula == NULL){ fprintf(stderr, "Memory error1\n"); exit(1); }
 
    if (verbose) {
	fprintf(stderr, "---------------------------\nroot is %s\n", root->me);
    } /*end if*/
    
        
    /*Loop while we haven't reached the root 
      after exploring it's right branch*/
    sprintf(formula, "(");
    while (! ((current == root) && (visited_right == 1)) ) {
	
	if (visited_left == 1) {
	    visited_left = 0;
	} /*end if*/
	else {
	    if (current->left_kid != NULL) {
		current = current->left_kid;
		sprintf(formula, "%s(", formula);
		continue;
	    } /*end if*/
	} /*end else*/

	if (visited_right == 1) {
	    visited_right = 0;
	} /*end if*/
	else {
	    /*Add this node to the formula*/
	    switch (current->me[0]) {
		case '-' :
		case '>' :
		    sprintf(formula, "%s -> ", formula, current->me);
		    break;
		default :
		    sprintf(formula, "%s%s ", formula, current->me);
	    } /*end switch*/
	    
	    if (current->right_kid != NULL) {
		current = current->right_kid;
		sprintf(formula, "%s(", formula);
		continue;
	    } /*end if*/
	    else {
		if (current == root) {
		    visited_right = 1;
		} /*end if*/
	    } /*end else*/
	} /*end else*/

	if (current->parent != NULL) {
	    visited_left = 1;
	    sprintf(formula, "%s)", formula);
	    if (current->parent->right_kid == current) {
		visited_right = 1;
	    } /*end if*/
	    current = current->parent;
	} /*end if*/

	i++;
    } /*end while*/	
    sprintf(formula, "%s)", formula);

    if (verbose) {
	fprintf(stderr, "1Here is the formula from the parse tree:\n");
    } /*end if*/
    fprintf(stderr, "%s\n", formula);

    if (verbose) {
	fprintf(stderr, "formula length is %d\n", formula_length);
    } /*end if*/

    /*Clear memory*/
    if (formula != NULL) {
	if (verbose) {
	    fprintf(stderr, "1Freeing formula\n");
	} /*end if*/
	free(formula);
    } /*end if*/

    return;
} /*end printFormula*/


/* Function getSubformulaVar
   Purpose: return a string representing the subformula rooted
      at local_root, using _'s instead of ()'s so as to make the
      subformula into a variable name. 

   No fancy stuff like printSubformulaVar.

   Note: this could be written to use less memory by only storing the last
      string of ___'s and then printing them whenever a non-_ is printed.
      That would avoid trailing ___'s on the variable name.

   Note: memory should be freed after running this code:
    Clean up memory
    if (formula != NULL) {
	if (verbose) {
	    fprintf(stderr, "Freeing formula\n");
	} end if
	free(formula);
    } end if
*/
void getSubformulaVar(size_t formula_length, struct node *local_root, char *&subformula) {
    struct node *current = local_root;
    short visited_left=0, visited_right=0;
    int i;

    if (verbose == 1) {
	fprintf(stderr, "getSubformulaVar here!");
    } /*end if*/

    if (verbose == 1) {
	fprintf(stderr, "Getting subformula var for local root %s\n", local_root->me);
    } /*end if*/

    /*Error Check*/
    if((formula_length == 0) || (root == NULL)) {
	fprintf(stderr, "Warning: Can't print an empty subformula\n");
	return;
    } /*end if*/

    subformula = (char *)malloc(sizeof(char) * ((formula_length*2)+1));
    if (subformula == NULL){ fprintf(stderr, "Memory error4\n"); exit(1); }
    strcpy(subformula, "\0"); /*make sure subformula starts empty*/

    /*Check if we've got a leaf*/
    if ((current->left_kid == NULL) && (current->right_kid == NULL)) {
	sprintf(subformula, "%s", local_root->me);

	if (verbose == 1) {
	    fprintf(stderr, "Returning leaf %s\n", local_root->me);
	} /*end if*/

	return;
    } /*end if*/

    /*Check if we've got the negation of a leaf*/
    if ((current->left_kid == NULL) && 
	(current->me[0] == '~') &&
	(current->right_kid != NULL) &&
	(current->right_kid->right_kid == NULL)) {

	sprintf(subformula, "(! %s)", local_root->right_kid->me);

	if (verbose == 1) {
	    fprintf(stderr, "Returning ! leaf %s\n", local_root->right_kid->me);
	} /*end if*/

	return;
    } /*end if*/

    /*Start the variable name*/
    if (tgba == 0) {
	if (current->me[0] == 'X') {
	    sprintf(subformula, "EL");
	} /*end if*/
	else {
	    sprintf(subformula, "S");
	} /*end else*/
    } /*end if*/
    else { /*tgba*/
	/*No prefix for tgba*/
	/*Do nothing*/
    } /*end else*/
    sprintf(subformula, "%s_", subformula);

    /*Loop while we haven't reached the local_root 
      after exploring it's right branch*/
    while (! ((current == local_root) && (visited_right == 1)) ) {
	
	if (visited_left == 1) {
	    visited_left = 0;
	} /*end if*/
	else {
	    if (current->left_kid != NULL) {
		current = current->left_kid;
		sprintf(subformula, "%s_", subformula);
		continue;
	    } /*end if*/
	} /*end else*/

	if (visited_right == 1) {
	    visited_right = 0;
	} /*end if*/
	else {
	    if (current->me[0] == '~') {
		sprintf(subformula, "%s%s", subformula, "NOT");
	    } /*end if*/
	    else if (current->me[0] == '&') {
		sprintf(subformula, "%s%s", subformula, "AND");
	    } /*end if*/
	    else if (current->me[0] == '|') {
		sprintf(subformula, "%s%s", subformula, "OR");
	    } /*end if*/
	    else if ((current->me[0] == '-')
		     || (current->me[0] == '>')) {
		sprintf(subformula, "%s%s", subformula, "IMP");
	    } /*end if*/
	    else { /*just put in current->me as part of the variable name*/
		sprintf(subformula, "%s%s", subformula, current->me);
	    } /*end else*/

	    if (current->right_kid != NULL) {
		current = current->right_kid;
		sprintf(subformula, "%s_", subformula);
		continue;
	    } /*end if*/
	    else {
		if (current == local_root) {
		    visited_right = 1;
		} /*end if*/
	    } /*end else*/
	} /*end else*/

	if (current->parent != NULL) {
	    visited_left = 1;
	    sprintf(subformula, "%s_", subformula);
	    /*fprintf(stderr, "8formula so far: %s\n", subformula);*/
	    if (current->parent->right_kid == current) {
		visited_right = 1;
	    } /*end if*/
	    current = current->parent;
	} /*end if*/
	
    } /*end while*/

    /*Remove trailing '_'s from the subformula*/
    i = strlen(subformula) - 1;
    while( (i > 0) && (subformula[i] == '_')) {
	subformula[i] = '\0';
	i--;
    } /*end while*/

    return;
} /*end getSubformulaVar*/


/* Function getSubformula
   Purpose: return a string representing the subformula rooted
      at local_root, including both regular subformulas and variables. 

      Main purpose: For use in TGBA for the CadenceSMV no S-vars for U-subformulas fix --
      allows nesting of printSubformula which is necessary for this fix.

   No fancy stuff like printSubformulaVar.

   Note: this could be written to use less memory by only storing the last
      string of ___'s and then printing them whenever a non-_ is printed.
      That would avoid trailing ___'s on the variable name.

   Note: memory should be freed after running this code:
    Clean up memory
    if (formula != NULL) {
	if (verbose) {
	    fprintf(stderr, "Freeing formula\n");
	} end if
	free(formula);
    } end if
*/
void getSubformula(size_t formula_length, struct node *local_root, char *&subformula) {
    struct node *current = local_root;
    char *temp;               /*temporary string for copying parts of subformula*/
    short visited_left=0, visited_right=0, done = 0;
    int i = 0;

    KItem search;            /*a variable name to search for*/
    int used;                /*did we use this var already?*/

    if (verbose == 1) {
	fprintf(stderr, "getSubformula here!");
    } /*end if*/

    if (!tgba) {
	fprintf(stderr, "ERROR: get Subformula not defined for GBA!!!\n");
	exit(1);
    } /*end if*/

    /*Error Check*/
    if((formula_length == 0) || (current == NULL)) {
	fprintf(stderr, "Warning: Can't get an empty subformula\n");
	return;
    } /*end if*/

    subformula = (char *)malloc(sizeof(char) * ((formula_length*2)+1));
    if (subformula == NULL){ fprintf(stderr, "Memory error1\n"); exit(1); }
 
    if (verbose) {
	fprintf(stderr, "---------------------------\nroot is %s\n", local_root->me);
    } /*end if*/
    
    subformula = (char *)malloc(sizeof(char) * ((formula_length*2)+1));
    if (subformula == NULL){ fprintf(stderr, "Memory error4\n"); exit(1); }
    strcpy(subformula, "\0"); /*make sure subformula starts empty*/

    /*Check if we've got a leaf*/
    if ((current->left_kid == NULL) && (current->right_kid == NULL)) {
	sprintf(subformula, "%s", local_root->me);

	if (verbose == 1) {
	    fprintf(stderr, "Returning leaf %s\n", local_root->me);
	} /*end if*/

	return;
    } /*end if*/


    /*Loop while we haven't reached the root 
      after exploring it's right branch*/
    sprintf(subformula, "(");
    while (! ((current == local_root) && (visited_right == 1)) ) {

	if (visited_left == 1) {
	    visited_left = 0;
	} /*end if*/
	else {
	    /*Add special nodes to the subformula without traversing their sub-trees*/
	    /*These are nodes with left kids which are represented as variables*/
	    switch (current->me[0]) {
		case 'U' :
		    if (tgba) {
			/*Print only EL-vars for U-subformulas b/c of CadenceSMV substitution bug*/
			getSubformulaVar(formula_length, current, temp);
			sprintf(subformula, "%sEL%s", subformula, temp);
			
			done = 1;

			break;
		    } /*end if tgba*/

		case 'R' :
		case 'G' :
		case 'F' :
		    getSubformulaVar(formula_length, current, temp);

		    if (tgba == 0) {
			sprintf(subformula, "%s%s", subformula, temp);
		    } /*end if*/
		    else { /*tgba*/
			sprintf(subformula, "%sS%s", subformula, temp);
		    } /*end else*/
		    done = 1;
	    
		    visited_right = 1;
		    break;
		case 'X' :
		    getSubformulaVar(formula_length, current, temp);

		    if (tgba == 0) {
			sprintf(subformula, "%s%s", subformula, temp);
		    } /*end if*/
		    else { /*tgba*/
		      sprintf(subformula, "%sS%s", subformula, temp);
		    } /*end else*/
		    done = 1;

		    visited_right = 1;
		    break;
		default : done = 0; break;
	    } /*end switch*/
	     
	    if (done == 0) {
		if (current->left_kid != NULL) {
		    current = current->left_kid;
		    sprintf(subformula, "%s(", subformula);
		    continue;
		} /*end if*/
	    } /*end if*/
	    else if (current == local_root) {
		break;
	    } /*end if*/
	} /*end else*/

	if (visited_right == 1) {
	    /*skipping right descent*/
	    visited_right = 0;
	} /*end if*/
	else {
	    /*Add this node to the subformula*/
	    switch (current->me[0]) {
		case '~' : /*SMV uses ! for not instead*/
		    sprintf(subformula, "%s!", subformula);
		    
		    /*fprintf(stderr, "1subformula so far: %s\n", subformula);*/

		    if (current->right_kid != NULL) {
			current = current->right_kid;
			sprintf(subformula, "%s(", subformula);
			continue;
		    } /*end if*/
		    else {
			if (current == local_root) {
			    visited_right = 1;
			} /*end if*/
		    } /*end else*/
		    break;

		case '-' : 
		case '>' :
		    sprintf(subformula, "%s->", subformula);
		    
		    if (current->right_kid != NULL) {
			current = current->right_kid;
			sprintf(subformula, "%s(", subformula);
			continue;
		    } /*end if*/
		    else {
			if (current == local_root) {
			    visited_right = 1;
			} /*end if*/
		    } /*end else*/
		    break;

		case 'U' : /*for SMV bug only*/
		    break; 
    
		default : 
		    sprintf(subformula, "%s%s ", subformula, current->me);
		    
		    if (current->right_kid != NULL) {
			current = current->right_kid;
			sprintf(subformula, "%s(", subformula);
			continue;
		    } /*end if*/
		    else {
			if (current == local_root) {
			    visited_right = 1;
			} /*end if*/
		    } /*end else*/

		    break;
	    } /*end switch*/
	    
	} /*end else*/

	if (current->parent != NULL) {
	    visited_left = 1;
	    sprintf(subformula, "%s)", subformula);
	    if (current->parent->right_kid == current) {
		visited_right = 1;
	    } /*end if*/
	    current = current->parent;
	} /*end if*/

	i++;
    } /*end while*/	
    sprintf(subformula, "%s)", subformula);

    if (verbose) {
	fprintf(stderr, "Here is the subformula from the parse tree:\n");
	fprintf(stderr, "%s\n", subformula);
	fprintf(stderr, "subformula length is %d\n", formula_length);
    } /*end if*/

    return;

} /*end getSubformula*/



/* void printSubformulahuman(size_t formula_length, struct node *local_root, FILE *MYOUT)

Purpose: provide "resolution" capability by printing the subformula rooted at local_root
         to the FILE *MYOUT. Prints the formula exactly as printFormulahuman does.
*/

void printSubformulahuman(size_t formula_length, struct node *local_root, FILE *MYOUT) {
    struct node *current = local_root;
    char *subformula;         /*the string representing the subformula*/
    char *temp;               /*temporary string for copying parts of subformula*/
    short visited_left=0, visited_right=0, done = 0;
    int i = 0;

    KItem search;            /*a variable name to search for*/
    int used;                /*did we use this var already?*/

    /*Error Check*/
    if((formula_length == 0) || (current == NULL)) {
	fprintf(stderr, "Warning: Can't print an empty subformula\n");
	return;
    } /*end if*/

    subformula = (char *)malloc(sizeof(char) * ((formula_length*2)+1));
    if (subformula == NULL){ fprintf(stderr, "Memory error1\n"); exit(1); }
 
    if (verbose) {
	fprintf(stderr, "---------------------------\nroot is %s\n", local_root->me);
    } /*end if*/
    
        
    /*Check if we've got a leaf*/
    if ((current->left_kid == NULL) && (current->right_kid == NULL)) {
	fprintf(MYOUT, "%s", local_root->me);

	if (verbose == 1) {
	    fprintf(stderr, "Printing leaf1 %s\n", local_root->me);
	} /*end if*/

	return;
    } /*end if*/

    /*Loop while we haven't reached the root 
      after exploring it's right branch*/
    sprintf(subformula, "(");
    while (! ((current == local_root) && (visited_right == 1)) ) {
	
	if (visited_left == 1) {
	    visited_left = 0;
	} /*end if*/
	else {
	    if (current->left_kid != NULL) {
		current = current->left_kid;
		sprintf(subformula, "%s(", subformula);
		continue;
	    } /*end if*/
	} /*end else*/

	if (visited_right == 1) {
	    visited_right = 0;
	} /*end if*/
	else {
	    /*Add this node to the subformula*/
	    switch (current->me[0]) {
		case '~' : /*SMV uses ! for not instead*/
		    sprintf(subformula, "%s!", subformula);
		    break;
    
		case '-' : /*make sure -> is written correctly*/
		case '>' :
		    sprintf(subformula, "%s->", subformula);
		    break;
		    
		default : 
		    sprintf(subformula, "%s%s ", subformula, current->me);
		    break;
	    } /*end switch*/
	    if (current->right_kid != NULL) {
		current = current->right_kid;
		sprintf(subformula, "%s(", subformula);
		continue;
	    } /*end if*/
	    else {
		if (current == local_root) {
		    visited_right = 1;
		} /*end if*/
	    } /*end else*/
	} /*end else*/

	if (current->parent != NULL) {
	    visited_left = 1;
	    sprintf(subformula, "%s)", subformula);
	    if (current->parent->right_kid == current) {
		visited_right = 1;
	    } /*end if*/
	    current = current->parent;
	} /*end if*/

	i++;
    } /*end while*/	
    sprintf(subformula, "%s)", subformula);

    if (verbose) {
	fprintf(stderr, "Here is the subformula from the parse tree:\n");
	fprintf(stderr, "%s\n", subformula);
	fprintf(stderr, "subformula length is %d\n", formula_length);
    } /*end if*/
    fprintf(MYOUT, "%s", subformula);

    /*Clear memory*/
    if (subformula != NULL) {
	if (verbose) {
	    fprintf(stderr, "Freeing subformula\n");
	} /*end if*/
	free(subformula);
    } /*end if*/

    return;
} /*end printSubformulahuman*/



/* void printSubformula(size_t formula_length, struct node *local_root, FILE *MYOUT)

Purpose: provide "resolution" capability by printing the subformula rooted at local_root
         to the FILE *MYOUT. Prints the formula exactly as printFormula does except
         instead of printing X-expressions, it uses the EL_-var assigned to these expressions.
*/

void printSubformula(size_t formula_length, struct node *local_root, FILE *MYOUT) {
    struct node *current = local_root;
    char *subformula;         /*the string representing the subformula*/
    char *temp;               /*temporary string for copying parts of subformula*/
    short visited_left=0, visited_right=0, done = 0;
    int i = 0;

    KItem search;            /*a variable name to search for*/
    int used;                /*did we use this var already?*/

    if (verbose == 1) {
	fprintf(stderr, "printSubformula here!");
    } /*end if*/

    /*Error Check*/
    if((formula_length == 0) || (current == NULL)) {
	fprintf(stderr, "Warning: Can't print an empty subformula\n");
	return;
    } /*end if*/

    subformula = (char *)malloc(sizeof(char) * ((formula_length*2)+1));
    if (subformula == NULL){ fprintf(stderr, "Memory error1\n"); exit(1); }
 
    if (verbose) {
	fprintf(stderr, "---------------------------\nroot is %s\n", local_root->me);
    } /*end if*/
    
        
    /*Check if we've got a leaf*/
    if ((current->left_kid == NULL) && (current->right_kid == NULL)) {
	fprintf(MYOUT, "%s", local_root->me);

	if (verbose == 1) {
	    fprintf(stderr, "Printing leaf2 %s\n", local_root->me);
	} /*end if*/

	return;
    } /*end if*/

    /*Loop while we haven't reached the root 
      after exploring it's right branch*/
    sprintf(subformula, "(");
    while (! ((current == local_root) && (visited_right == 1)) ) {
	
	if (visited_left == 1) {
	    visited_left = 0;
	} /*end if*/
	else {
	    /*Add special nodes to the subformula without traversing their sub-trees*/
	    /*These are nodes with left kids which are represented as variables*/
	    switch (current->me[0]) {
		case 'U' :
		    //@//if (tgba) {
			/*don't print vars for U-subformulas b/c of CadenceSMV substitution bug*/
			// /*fprintf(stderr, "1subformula so far: %s\n", subformula);*/
// 			getSubformula(formula_length, current->right_kid, temp);
// 			sprintf(subformula, "%s%s | (", subformula, temp);
// 			/*fprintf(stderr, "2subformula so far: %s\n", subformula);*/
// 			getSubformula(formula_length, current->left_kid, temp);
			
// 			if (smvFlag == 's') { /*SAL*/
// 			    sprintf(subformula, "%s AND ", subformula, temp);
// 			} /*end if SAL*/
// 			else { /*Cadence SMV or NuSMV*/
// 			    sprintf(subformula, "%s%s & ", subformula, temp);
// 			    /*fprintf(stderr, "3subformula so far: %s\n", subformula);*/
// 			} /*end else*/
			
			//@//getSubformulaVar(formula_length, current, temp);
//			sprintf(subformula, "%sP%s & (next(EL%s)))", subformula, temp, temp);
			//@//sprintf(subformula, "%s(EL%s)", subformula, temp, temp);
			/*fprintf(stderr, "4subformula so far: %s\n", subformula);*/
			
			//@//done = 1;

			//@//break;
		    //@//} /*end if tgba*/

		case 'R' :
		case 'G' :
		case 'F' :
		    getSubformulaVar(formula_length, current, temp);
		    if (tgba == 0) {
			sprintf(subformula, "%s%s", subformula, temp);
		    } /*end if*/
		    else { /*tgba*/
			sprintf(subformula, "%sEL%s", subformula, temp); //HERE444
		    } /*end else*/
		    done = 1;
	    
		    visited_right = 1;
		    break;
		case 'X' :
		    getSubformulaVar(formula_length, current, temp);
		    if (tgba == 0) {
			sprintf(subformula, "%s%s", subformula, temp);
		    } /*end if*/
		    else { /*tgba*/
		      sprintf(subformula, "%sS%s", subformula, temp);
		    } /*end else*/
		    done = 1;

		    visited_right = 1;
		    break;
		default : done = 0; break;
	    } /*end switch*/
	     
	    if (done == 0) {
		if (current->left_kid != NULL) {
		    current = current->left_kid;
		    sprintf(subformula, "%s(", subformula);
		    continue;
		} /*end if*/
	    } /*end if*/
	    else if (current == local_root) {
		break;
	    } /*end if*/
	} /*end else*/

	if (visited_right == 1) {
	    /*skipping right descent*/
	    visited_right = 0;
	} /*end if*/
	else {
	    /*Add this node to the subformula*/
	    switch (current->me[0]) {
		case '~' : /*SMV uses ! for not instead*/
		    sprintf(subformula, "%s!", subformula);
		    
		    if (current->right_kid != NULL) {
			current = current->right_kid;
			sprintf(subformula, "%s(", subformula);
			continue;
		    } /*end if*/
		    else {
			if (current == local_root) {
			    visited_right = 1;
			} /*end if*/
		    } /*end else*/
		    break;

		case '-' : /*make sure -> is written correctly*/
		case '>' :
		    sprintf(subformula, "%s->", subformula);
		    
		    if (current->right_kid != NULL) {
			current = current->right_kid;
			sprintf(subformula, "%s(", subformula);
			continue;
		    } /*end if*/
		    else {
			if (current == local_root) {
			    visited_right = 1;
			} /*end if*/
		    } /*end else*/
		    break;

		case 'U' : /*for SMV bug only*/
		    break; 
    
		default : 
		    sprintf(subformula, "%s%s ", subformula, current->me);
		    
		    if (current->right_kid != NULL) {
			current = current->right_kid;
			sprintf(subformula, "%s(", subformula);
			continue;
		    } /*end if*/
		    else {
			if (current == local_root) {
			    visited_right = 1;
			} /*end if*/
		    } /*end else*/

		    break;
	    } /*end switch*/
	    
	} /*end else*/

	if (current->parent != NULL) {
	    visited_left = 1;
	    sprintf(subformula, "%s)", subformula);
	    if (current->parent->right_kid == current) {
		visited_right = 1;
	    } /*end if*/
	    current = current->parent;
	} /*end if*/

	i++;
    } /*end while*/	
    sprintf(subformula, "%s)", subformula);

    if (verbose) {
	fprintf(stderr, "Here is the subformula from the parse tree:\n");
	fprintf(stderr, "%s\n", subformula);
	fprintf(stderr, "subformula length is %d\n", formula_length);
    } /*end if*/
    fprintf(MYOUT, "%s", subformula);

    /*Clear memory*/
    if (subformula != NULL) {
	if (verbose) {
	    fprintf(stderr, "Freeing subformula\n");
	} /*end if*/
	free(subformula);
    } /*end if*/

    return;
} /*end printSubformula*/



/* Function printSubformulaVar_makeGraph
   Purpose: print a subformula rooted at the input pointer to the
      output file, using _'s instead of ()'s so as to make the
      subformula into a variable name
   Returns: the id number of the subformula variable in the varList
*/
int printSubformulaVar_makeGraph(struct node *local_root) {
    struct node *current = local_root;
    int rootPtr = 0;          /*position of the root char in the subformula string*/
    char *subformula;         /*the string representing the subformula*/
    char *temp;               /*temporary string for copying parts of subformula*/
    short visited_left=0, visited_right=0;
    int varNum = -1;               /*the id number of this subformula*/
    int promiseVarNum = -1;        /*the id number of this subformula's promise variable*/
    int i;

    KItem search;             /*a variable name to search for*/
    int used;                 /*did we use this var already?*/

    if (verbose == 1) {
	fprintf(stderr, "printSubformulaVar_makeGraph here!");
    } /*end if*/

    /*Error Check*/
    if((formula_length == 0) || (current == NULL)) {
	fprintf(stderr, "Warning: Can't print an empty sub-formula\n");
	return -1;
    } /*end if*/

    subformula = (char *)malloc(sizeof(char) * ((formula_length*2)+1));
    if (subformula == NULL){ fprintf(stderr, "Memory error2\n"); exit(1); }
    temp       = (char *)malloc(sizeof(char) * ((formula_length*2)+1));
    if (temp == NULL){ fprintf(stderr, "Memory error3\n"); exit(1); }
    strcpy(subformula, "\0"); /*make sure subformula starts empty*/

    if (verbose) {
	fprintf(stderr, "---------------------------\nsub-root is %s\n", current->me);
    } /*end if*/
    /* First -- Build the subformula, note the root position in the string*/

    /*Loop while we haven't reached the root 
      after exploring it's right branch*/
    sprintf(subformula, "%s_", subformula); 
    while (! ((current == local_root) && (visited_right == 1)) ) {
	
	if (visited_left == 1) {
	    visited_left = 0;
	} /*end if*/
	else {
	    if (current->left_kid != NULL) {
		current = current->left_kid;
		sprintf(subformula, "%s_", subformula); /* _ for ( */
		continue;
	    } /*end if*/
	} /*end else*/

	if (visited_right == 1) {
	    visited_right = 0;
	} /*end if*/
	else {
	    /*Add this node to the formula*/
	    if (current->me[0] == '~') {
		sprintf(subformula, "%s%s", subformula, "NOT");
	    } /*end if*/
	    else if (current->me[0] == '&') {
		sprintf(subformula, "%s%s", subformula, "AND");
	    } /*end if*/
	    else if (current->me[0] == '|') {
		sprintf(subformula, "%s%s", subformula, "OR");
	    } /*end if*/
	    else if (current->me[0] == '-') {
		sprintf(subformula, "%s%s", subformula, "IMP");
	    } /*end if*/
	    else { /*just put in current->me as part of the variable name*/
		sprintf(subformula, "%s%s", subformula, current->me);
	    } /*end else*/

	    if (current == local_root) { /*record the position of the local root*/
		rootPtr = strlen(subformula) - 1;
		if (verbose) {
		    fprintf(stderr, "rootPtr is %d\n", rootPtr);
		} /*end if*/
	    } /*end if*/
	    if (current->right_kid != NULL) {
		current = current->right_kid;
		sprintf(subformula, "%s_", subformula);
		continue;
	    } /*end if*/
	} /*end else*/

	if (current->parent != NULL) {
	    visited_left = 1;
	    sprintf(subformula, "%s_", subformula);
	    if (current->parent->right_kid == current) {
		visited_right = 1;
	    } /*end if*/
	    current = current->parent;
	} /*end if*/
	
    } /*end while*/ 

    /*Remove trailing '_'s from the subformula*/
    i = strlen(subformula) - 1;
    while( (i > 0) && (subformula[i] == '_')) {
	subformula[i] = '\0';
	i--;
    } /*end while*/	

    if (verbose) {
	fprintf(stderr, "subformula is %s\n", subformula);
    } /*end if*/

    /*Check if we've already dealt with an identical subformula before*/
    search.setName(subformula);
    if ( ( (tgba == 0) && ( ! ( (varList.query(search) || funcList.query(search)) ) ))
	 || ((tgba) && ( ! (funcList.query(search)))) ) { 
        /*if it's not in varList or funcList, we haven't used this variable name yet*/
		
	if (tgba 
	    && (local_root == root)    /*Always print a var for the whole formula*/
	    && (root->me[0] != 'U')
	    && (root->me[0] != 'R')
	    && (root->me[0] != 'F')
	    && (root->me[0] != 'G')) { /*Avoid re-declaring temporal operators*/
	    fprintf(OUT, "EL%s : boolean;\n", subformula);
	    
	    /*Add the var to the list so we don't use it again*/
	    varNum = varList.addItem(search);
	    local_root->num = varNum; /*record the variable number*/
	    if (verbose == 1) {
		fprintf(stderr, "adding item %s to varlist1\n", search.getName().c_str());
	    } /*end if*/

	    if (varOrder != 'z') {
		/*Make self-loops at all vertices in the variable graph*/
		connect_graph(varNum, varNum);
	    } /*end if*/
	    
	    /*Add a transition for the whole formula*/
	    if (Xcounter > 0) {  fprintf(TOUT, " &\n"); }
	    Xcounter++;

	    if (sloppy) {
		if (smvFlag == 's') { /*SAL*/
		    fprintf(TOUT, "( EL%s -> (something) )", subformula);
		} /*end if*/
		else { /*Cadence SMV and NuSMV*/
		    fprintf(TOUT, "( EL%s -> (S%s) )", subformula, subformula);
		} /*end else*/
	    } /*end if*/
	    else { /*fussy*/
		if (smvFlag == 's') { /*SAL*/
		    fprintf(TOUT, "( EL%s = (something;) )", subformula);
		} /*end if*/
		else { /*Cadence SMV and NuSMV*/
		    fprintf(TOUT, "( EL%s = (S%s) )", subformula, subformula);
		} /*end else*/
	    } /*end else*/
	} /*end if TGBA and root*/
	    
	switch (local_root->me[0]) {
	    case 'X' : 
		if (tgba == 0) {
		    fprintf(OUT, "EL%s : boolean;\n", subformula);
		    
		    /*Add the var to the list so we don't use it again*/
		    varNum = varList.addItem(search);
		    local_root->num = varNum; /*record the variable number*/
		    if (verbose == 1) {
			fprintf(stderr, "adding item %s to varlist2\n", search.getName().c_str());
		    } /*end if*/
		    
		    if (varOrder != 'z') {
			/*Make self-loops at all vertices in the variable graph*/
			connect_graph(varNum, varNum);
		    } /*end if*/

		    /*Add a transition for the var*/
		    if (Xcounter == 0) { 
			if (smvFlag == 's') { fprintf(TOUT, "       "); } /*indent SAL module*/
			fprintf(TOUT, "( EL");
		    } /*end if*/
		    else {
			if (smvFlag == 's') { fprintf(TOUT, "       "); } /*indent SAL module*/
			fprintf(TOUT, " &\n( EL");
		    } /*end else*/
		    Xcounter++;
		    
		    if (sloppy) {
			if (smvFlag == 's') { /*SAL*/
			    fprintf(TOUT, "%s -> (something)", subformula);
			} /*end if*/
			else { /*Cadence SMV and NuSMV*/
			    fprintf(TOUT, "%s -> (next(", subformula);
			} /*end else*/
		    } /*end if*/
		    else {
			if (smvFlag == 's') { /*SAL*/
			    fprintf(TOUT, "%s = (something) )", subformula);
			} /*end if*/
			else { /*Cadence SMV and NuSMV*/
			    fprintf(TOUT, "%s = (next(", subformula);
			} /*end else*/
		    } /*end else*/
		    
		    getSubformulaVar(formula_length, local_root->right_kid, temp);
		    fprintf(TOUT, "%s) ) )", temp);
		} /*end if*/
		else { /*tgba*/ 

		    fprintf(SOUT, "S%s := (next(", subformula);
		    /*for tgba, everything rooted from an X is a variable*/

		    /*Add the characteristic function to the list so we don't define it again*/
		    funcList.addItem(search);
		    if (verbose == 1) {
			fprintf(stderr, "adding item %s to funcList1\n", search.getName().c_str());
		    } /*end if*/

		    if (local_root->right_kid->right_kid == NULL) { /*skip leaves*/
			/* || ((current->temp_kid != 1)) ) { /*skip non-temporal kids*/
			fprintf(SOUT, "%s));\n", local_root->right_kid->me);
			//fprintf(stderr, "breaking!!!\n"); //DEBUG
			break;
		    } /*end if*/

		    i = strlen(subformula+rootPtr+1);
		    strcpy(temp, subformula+rootPtr+1);
		    temp[i] = '\0';
		    fprintf(SOUT, "EL%s));\n", temp);
		    
		    /*Declare a variable for the right kid of X*/
		    search.setName(temp);

		    if ( ( ! ( varList.query(search) ) )  /*we haven't been here before*/
			 /*also skip temporal vars which will have their own definitions*/
			 && ((current->temp_kid == 0) || (current->right_kid->me[0] == 'X')) ) {

			fprintf(OUT, "EL%s : boolean;\n", temp);
		    
			/*Add the var to the list so we don't use it again*/
			varNum = varList.addItem(search);
			if (current->right_kid == NULL ) {
			    fprintf(stderr, "ERROR: Malformed parse tree -- X with no right kid\n");
			    exit(1);
			} /*end if*/
			else {
			    current->right_kid->num = varNum;
			} /*end else*/
			//local_root->num = varNum; /*record the variable number*/
			if (verbose == 1) {
			    fprintf(stderr, "adding item %s to varlist3\n", search.getName().c_str());
			} /*end if*/
			
			if (varOrder != 'z') {
			    /*Make self-loops at all vertices in the variable graph*/
			    connect_graph(varNum, varNum);
			} /*end if*/
			
			if (Xcounter == 0) { 
			    if (smvFlag == 's') { fprintf(TOUT, "       "); } /*indent SAL module*/
			    fprintf(TOUT, "( EL");
			} /*end if*/
			else {
			    if (smvFlag == 's') { fprintf(TOUT, "       "); } /*indent SAL module*/
			    fprintf(TOUT, " &\n( EL");
			} /*end else*/
			Xcounter++;

			if (verbose) {
			    printSubformulahuman(formula_length, local_root, stderr);
			    fprintf(stderr, "X-kid was %s; temp_kid was %d", local_root->right_kid->me, local_root->temp_kid);
			    fprintf(stderr, "\n");
			} /*end if*/

			if (sloppy) {
			    if (smvFlag == 's') { /*SAL*/
				fprintf(TOUT, "%s -> (", temp);
			    } /*end if*/
			    else { /*Cadence SMV and NuSMV*/
				fprintf(TOUT, "%s -> (", temp);
			    } /*end else*/
			} /*end if*/
			else {
			    if (smvFlag == 's') { /*SAL*/
				fprintf(TOUT, "%s = (", temp);
			    } /*end if*/
			    else { /*Cadence SMV and NuSMV*/
				fprintf(TOUT, "%s = (", temp);
			    } /*end else*/
			} /*end else*/
			printSubformula(formula_length, local_root->right_kid, TOUT);
			fprintf(TOUT, ") ) ");
		    } /*end if*/
		    else { /*variable already in varList*/ 
			if (verbose) {
			    fprintf(stderr, "Avoiding2 redefinition of %s (var %d)\n", temp, varNum);
			} /*end if*/
		    } /*end else*/

		} /*end else*/
		break;
	    case '~' : /*fprintf(SOUT, "S");*/
		if ((current == root) 
		    || (current->temp_kid == 1) /*temporal kid; need a S-function definition*/
		    || ((current->parent!= NULL) && (current->parent->me[0] == 'X'))) { 
		    
		    /*Print a definition for the characteristic function*/
		    if (smvFlag == 's') { 
			fprintf(SOUT, "       "); /*indent SAL module*/
			fprintf(SOUT, "S%s = !", subformula);
		    } /*end if*/
		    else {
			fprintf(SOUT, "S%s := !", subformula);
		    } /*end else*/
		    printSubformula(formula_length, local_root->right_kid, SOUT);
		    fprintf(SOUT, ";\n");

		    /*Add the characteristic function to the list so we don't define it again*/
		    funcList.addItem(search);
		    if (verbose == 1) {
			fprintf(stderr, "adding item %s to funcList2\n", search.getName().c_str());
		    } /*end if*/
		} /*end if*/

		break;
	    case '&' : /*check this still works right for gba*/
		if ((current == root) /*gba or tgba*/
		    || ((tgba) && (current->temp_kid == 1)) /*temporal kid; need a S-function definition*/
		    || ((current->parent!= NULL) && (current->parent->me[0] == 'X'))) { 
		    
		    if (smvFlag == 's') { 
			fprintf(SOUT, "       "); /*indent SAL module*/
			fprintf(SOUT, "S%s = ", subformula);
		    } /*end if*/
		    else {
			fprintf(SOUT, "S%s := ", subformula);
		    } /*end else*/
		    if (verbose) {
			fprintf(stderr, "rootPtr is %d\n", rootPtr);
		    } /*end if*/
		    
		    printSubformula(formula_length, local_root->left_kid, SOUT);
		    fprintf(SOUT, " & ");
		    printSubformula(formula_length, local_root->right_kid, SOUT);
		    fprintf(SOUT, ";\n"); //HERE555
		    
		    /*Add the characteristic function to the list so we don't define it again*/
		    funcList.addItem(search);
		    if (verbose == 1) {
			fprintf(stderr, "adding item %s to funcList3\n", search.getName().c_str());
		    } /*end if*/
		} /*end if*/
		break;
	    case '|' :
		if ((current == root) 
		    || (current->temp_kid == 1) /*temporal kid; need a S-function definition*/
		    || ((current->parent!= NULL) && (current->parent->me[0] == 'X'))) { 

		    if (smvFlag == 's') { 
			fprintf(SOUT, "       "); /*indent SAL module*/
			fprintf(SOUT, "S%s = ", subformula);
		    } /*end if*/
		    else {
			fprintf(SOUT, "S%s := ", subformula);
		    } /*end else*/
		    
		    printSubformula(formula_length, local_root->left_kid, SOUT);
		    fprintf(SOUT, " | ");
		    printSubformula(formula_length, local_root->right_kid, SOUT);
		    fprintf(SOUT, ";\n");
		    
		    if (verbose) {
			fprintf(stderr, "rootPtr is %d\n", rootPtr);
		    } /*end if*/
		    
		    /*Add the characteristic function to the list so we don't define it again*/
		    funcList.addItem(search);
		    if (verbose == 1) {
			fprintf(stderr, "adding item %s to funcList4\n", search.getName().c_str());
		    } /*end if*/
		} /*end if*/
		break;
	    case '-' :
	    case '>' :
		if ((current == root) 
		    || (current->temp_kid == 1) /*temporal kid; need a S-function definition*/
		    || ((current->parent!= NULL) && (current->parent->me[0] == 'X'))) { 

		    if (smvFlag == 's') { 
			fprintf(SOUT, "       "); /*indent SAL module*/
			fprintf(SOUT, "S%s = ", subformula);
		    } /*end if*/
		    else {
			fprintf(SOUT, "S%s := ", subformula);
		    } /*end else*/
		    
		    printSubformula(formula_length, local_root->left_kid, SOUT);
		    fprintf(SOUT, " -> ");
		    printSubformula(formula_length, local_root->right_kid, SOUT);
		    fprintf(SOUT, ";\n");		    
		    
		    if (verbose) {
			fprintf(stderr, "rootPtr is %d\n", rootPtr);
		    } /*end if*/
		    
		    /*Add the characteristic function to the list so we don't define it again*/
		    funcList.addItem(search);
		    if (verbose == 1) {
			fprintf(stderr, "adding item %s to funcList5\n", search.getName().c_str());
		    } /*end if*/
		} /*end if*/
		break;
	    case 'U' : 
		i = strlen(subformula+rootPtr+1);
		strcpy(temp, subformula+rootPtr+1);
		temp[i] = '\0';
		
		if (tgba) { /*P-vars*/
		    /*Check if we've declared this variable yet*/
		    search.setName(subformula);
		    used = varList.query(search);
		    if (used == 0) { /*we haven't used this variable name yet*/
			/*if this if-statement is ever changed, the variable ordering connection must be changed*/
			
			if (smvFlag == 's') { /*SAL*/
			    /*fprintf(FOUT, "\n\n     fairness%d: THEOREM main |-  NOT EL%s OR S%s\n", 
			      fairnum, subformula, temp); /*Use promise var now*/
			    fprintf(FOUT, "\n\n     fairness%d: THEOREM main |-  NOT P%s\n", 
				    fairnum, subformula);
			} /*end if SAL*/
			
			/*Cadence SMV or NuSMV*/
			else if (smvFlag == 'n') { /*NuSMV*/
			    /*fprintf(FOUT, "\nJUSTICE   (!EL%s | ", subformula); /*Use promise var now*/
			    fprintf(FOUT, "\nJUSTICE   (!P%s)\n", subformula);
			} /*end if*/
			else {/*Cadence SMV*/
			    /*fprintf(FOUT, "\nFAIRNESS   (!EL%s | ", subformula);*/
			    /*Use promise var now*/
			    fprintf(FOUT, "\nFAIRNESS   (!P%s)\n", subformula, subformula);
			} /*end if Cadence SMV*/
			fairnum++;
			
			fprintf(OUT, "P%s: boolean;\n", subformula); /*promise variable*/
			if (define_P_vars) {
			    /*try defining the promise variable too*/
			    if (Xcounter > 0) {  fprintf(TOUT, " &\n"); }
			    Xcounter++;
			    fprintf(TOUT, "( P%s = (EL%s & (!", subformula, subformula);
			    //fprintf(TOUT, "( P%s = ((! EL%s) | (", subformula, subformula);
			    printSubformula(formula_length, local_root->right_kid, TOUT);
			    fprintf(TOUT, ")) )"); /*end promise var definition*/
			} /*end if*/

			/*Add the var to the list so we can connect it into the var graph*/
			sprintf(temp, "%s%s", "P", subformula);
			search.setName(temp);
			promiseVarNum = varList.addItem(search);
			/*local_root->num = varNum; Not for promise vars /*record the variable number*/
			if (verbose == 1) {
			    fprintf(stderr, "U: adding item %s to varlist4\n", search.getName().c_str());
			} /*end if*/
			/*fprintf(stderr, "U: adding item %s to varlist\n", search.getName().c_str());*/
			
			if (varOrder != 'z') {
			    /*Make self-loops at all vertices in the variable graph*/
			    //fprintf(stderr, "connect5\n");
			    connect_graph(promiseVarNum, promiseVarNum);
			    /*fprintf(stderr, "Connecting1 var %d to var %d\n", varNum, varNum);*/
			} /*end if*/

		    } /*end if used*/
		    /*No else here b/c P-vars aren't connected to the rest of the tree*/
		    search.setName(subformula);

		    if ( ! ( varList.query(search) ) ) {/*we haven't been here before*/
			fprintf(OUT, "EL%s : boolean;\n", subformula);

			if (Xcounter == 0) { 
			    if (smvFlag == 's') { fprintf(TOUT, "       "); } /*indent SAL module*/
			    fprintf(TOUT, "( ");
			} /*end if*/
			else {
			    if (smvFlag == 's') { fprintf(TOUT, "       "); } /*indent SAL module*/
			    fprintf(TOUT, " &\n( ");
			} /*end else*/
			Xcounter++;
			
			if (sloppy) {
			    if (smvFlag == 's') { /*SAL*/
				fprintf(TOUT, "EL%s -> (S%s) )", subformula, subformula);
			    } /*end if*/
			    else { /*Cadence SMV and NuSMV*/
				fprintf(TOUT, "EL%s -> (S%s) )", subformula, subformula);
			    } /*end else*/
			} /*end if*/
			else {
			    if (smvFlag == 's') { /*SAL*/
				fprintf(TOUT, "EL%s = (S%s) )", subformula, subformula);
			    } /*end if*/
			    else { /*Cadence SMV and NuSMV*/
				fprintf(TOUT, "EL%s = (S%s) )", subformula, subformula);
			    } /*end else*/
			} /*end else*/
			
			/*Add the var to the list so we don't use it again*/
			varNum = varList.addItem(search);
			local_root->num = varNum; /*record the variable number*/
			if (verbose == 1) {
			    fprintf(stderr, "U: adding item %s to varlist4\n", search.getName().c_str());
			} /*end if*/
			//fprintf(stderr, "U: adding item %s to varlist as var #%d\n", search.getName().c_str(), varNum);
			
			if (varOrder != 'z') {
			    /*Make self-loops at all vertices in the variable graph*/
			    connect_graph(varNum, varNum);
			    connect_graph(varNum, promiseVarNum);
			} /*end if*/
			
			
			if (smvFlag == 's') { /*SAL*/
			    fprintf(SOUT, "       "); /*indent SAL module*/
			    fprintf(SOUT, "S%s = ( (", subformula);
			} /*end if*/
			else {
			    fprintf(SOUT, "S%s := ( (", subformula);
			} /*end else*/

			printSubformula(formula_length, local_root->right_kid, SOUT);
			if (smvFlag == 's') { fprintf(SOUT, ") OR ("); } /*SAL*/
			else { fprintf(SOUT, ") | ("); }                 /*not SAL*/
			printSubformula(formula_length, local_root->left_kid, SOUT);
			
			if (smvFlag == 's') { /*SAL*/
			    /*changed for resolution*/
			    /*fprintf(SOUT, "%s AND S_X%s);\n", temp, subformula);*/
			    fprintf(SOUT, "AND P%s AND (next(EL%s))));\n", subformula, subformula);
			} /*end if SAL*/
			else { /*Cadence SMV or NuSMV*/
			    /*changed for resolution*/
			    /*fprintf(SOUT, "%s & S_X%s);\n", temp, subformula);*/
			    /*resolution:out fprintf(SOUT, "%s & EL_X%s);\n", temp, subformula);*/
			    fprintf(SOUT, " & P%s & (next(EL%s))));\n", subformula, subformula);
			} /*end else*/

			/*Add the characteristic function to the list so we don't define it again*/
			funcList.addItem(search);
			if (verbose == 1){
			    fprintf(stderr, "adding item %s to funcList6\n", search.getName().c_str());
			} /*end if*/
			
		    } /*end if*/
		    else { /*variable already in varList*/ 
			varNum = ((KItem)(varList.find(search))).getInfo();
			local_root->num = varNum; /*record the variable number*/
			if (verbose) {
			    fprintf(stderr, "Avoiding3 redefinition of %s (var %d)\n", subformula, varNum);
			} /*end if*/
		    } /*end else*/
		    		    
		} /*end if(tgba)*/
		else { /*GBA, NOT TGBA*/

		    if (smvFlag == 's') { /*SAL*/
			fprintf(FOUT, "\n\n     fairness%d: THEOREM main |-  NOT S%s OR ", 
				fairnum, subformula); 
			printSubformula(formula_length, local_root->right_kid, FOUT);
			fprintf(FOUT, "\n");
			fprintf(SOUT, "       "); /*indent SAL module*/
			
			fprintf(SOUT, "S%s = ", subformula);
			printSubformula(formula_length, local_root->right_kid, SOUT);
			fprintf(SOUT, " OR (");
		    } /*end if SAL*/
		    else { /*Cadence SMV or NuSMV*/
			if (smvFlag == 'n') { /*NuSMV*/
			    fprintf(FOUT, "\nJUSTICE   (!S%s | ", subformula);
			    printSubformula(formula_length, local_root->right_kid, FOUT);
			    fprintf(FOUT, ")\n");
			} /*end if*/
			else {/*Cadence SMV*/
			    fprintf(FOUT, "\nFAIRNESS   (!S%s | ", subformula);
			    printSubformula(formula_length, local_root->right_kid, FOUT);
			    fprintf(FOUT, ")\n");
			} /*end else*/
			
			fprintf(SOUT, "S%s := ", subformula);
			printSubformula(formula_length, local_root->right_kid, SOUT);
			fprintf(SOUT, " | (");
		    } /*end else*/

		    printSubformula(formula_length, local_root->left_kid, SOUT);
		    fairnum++; /*we just added another fairness statement*/
		    
		    if (smvFlag == 's') { /*SAL*/
			/*changed for resolution*/
			/*fprintf(SOUT, "%s AND S_X%s);\n", temp, subformula);*/
			fprintf(SOUT, "%s AND EL_X%s);\n", temp, subformula);
		    } /*end if SAL*/
		    else { /*Cadence SMV or NuSMV*/
		      fprintf(SOUT, " & EL_X%s);\n", subformula);
		    } /*end else*/

		    /*Add the characteristic function to the list so we don't define it again*/
		    funcList.addItem(search);
		    if (verbose == 1){
			fprintf(stderr, "adding item %s to funcList7\n", search.getName().c_str());
		    } /*end if*/
		} /*end else*/		    

		if ( (tgba == 0) && (! ( (local_root->parent != NULL) 
					 && (local_root->parent->me[0] == 'X') ) ) ) {
		    /*Check if we've declared this variable yet*/
		    sprintf(temp, "_X%s", subformula); /*NEW*/
		    search.setName(temp);

		    used = varList.query(search);
		    if (used == 0) { /*we haven't used this variable name yet*/
			
			fprintf(OUT, "EL_X%s : boolean;\n", subformula); /*NEW*/
			
			/*Add a transition*/
			if (Xcounter == 0) { 
			    if (smvFlag == 's') { fprintf(TOUT, "       "); } /*indent SAL module*/
			    fprintf(TOUT, "( EL");
			} /*end if*/
			else {
			    if (smvFlag == 's') { fprintf(TOUT, "       "); } /*indent SAL module*/
			    fprintf(TOUT, " &\n( EL");
			} /*end else*/
			Xcounter++;
			
			if (sloppy) {
			    if (smvFlag == 's') { /*SAL*/
				fprintf(TOUT, "_X%s -> (something )", subformula);
			    } /*end if*/
			    else { /*Cadence SMV and NuSMV*/
				fprintf(TOUT, "_X%s -> (next(", subformula);
			    } /*end else*/
			} /*end if*/
			else {
			    if (smvFlag == 's') { /*SAL*/
				fprintf(TOUT, "_X%s = (something;) )", subformula);
			    } /*end if*/
			    else { /*Cadence SMV and NuSMV*/
				fprintf(TOUT, "_X%s = (next(", subformula);
			    } /*end else*/
			} /*end else*/
			getSubformulaVar(formula_length, local_root, temp);
			fprintf(TOUT, "%s) ))", temp);
		    
			/*Add the var to the list so we don't use it again*/
			varNum = varList.addItem(search);
			local_root->num = varNum; /*record the variable number*/
			if (verbose == 1) {
			    fprintf(stderr, "adding item %s to varlist5\n", search.getName().c_str());
			} /*end if*/
			
			if (varOrder != 'z') {
			    /*Make self-loops at all vertices in the variable graph*/
			    connect_graph(varNum, varNum);
			} /*end if*/
		    } /*end if*/
		    else { /*variable already in varList*/
			varNum = ((KItem)(varList.find(search))).getInfo();
			local_root->num = varNum; /*record the variable number*/
			if (verbose) {
			    fprintf(stderr, "Avoiding4 redefinition of %s (var %d)\n", subformula, varNum);
			} /*end if*/
		    } /*end else*/
		} /*end if*/
		break;
	    case 'R' : 
		i = strlen(subformula+rootPtr+1);
		strcpy(temp, subformula+rootPtr+1);
		temp[i] = '\0';
		
		if (tgba) {
		    /*Check if we've declared this variable yet*/
		    search.setName(subformula);
		    used = varList.query(search);
		    if (used == 0) { /*we haven't used this variable name yet*/
			/*if this if-statement is ever changed, the variable ordering connection must be changed*/
			
			if (smvFlag == 's') { /*SAL*/
			    fprintf(SOUT, "       "); /*indent SAL module*/
			    fprintf(SOUT, "S%s = ", subformula);
			} /*end if*/
			else {
			    fprintf(SOUT, "S%s := ", subformula);
			} /*end else*/
			
			printSubformula(formula_length, local_root->right_kid, SOUT);
			fprintf(SOUT, " & (");
			printSubformula(formula_length, local_root->left_kid, SOUT);
		    
		    
			if (smvFlag == 's') { /*SAL*/
			    fprintf(SOUT, " OR (next(EL%s)));\n", subformula);
			} /*end if*/
			else { /*Cadence SMV or NuSMV*/
			    fprintf(SOUT, " | (next(EL%s)));\n", subformula);
			} /*end else*/
		    
			/*Add the characteristic function to the list so we don't define it again*/
			funcList.addItem(search);
			if (verbose == 1) {
			    fprintf(stderr, "adding item %s to funcList8\n", search.getName().c_str());
			} /*end if*/
		    } /*end if*/

		    search.setName(subformula);
		    if ( ! ( varList.query(search) ) ) {/*we haven't been here before*/

			fprintf(OUT, "EL%s : boolean;\n", subformula); /*NEW*/
			
			if (Xcounter == 0) { 
			    if (smvFlag == 's') { fprintf(TOUT, "       "); } /*indent SAL module*/
			    fprintf(TOUT, "( EL");
			} /*end if*/
			else {
			    if (smvFlag == 's') { fprintf(TOUT, "       "); } /*indent SAL module*/
			    fprintf(TOUT, " &\n( EL");
			} /*end else*/
			Xcounter++;
			
			if (sloppy) {
			    if (smvFlag == 's') { /*SAL*/
				fprintf(TOUT, "%s -> (S%s) )", subformula, subformula);
			    } /*end if*/
				    else { /*Cadence SMV and NuSMV*/
					fprintf(TOUT, "%s -> (S%s) )", subformula, subformula);
				    } /*end else*/
			} /*end if*/
			else {
			    if (smvFlag == 's') { /*SAL*/
				fprintf(TOUT, "%s = (S%s) )", subformula, subformula);
			    } /*end if*/
			    else { /*Cadence SMV and NuSMV*/
				fprintf(TOUT, "%s = (S%s) )", subformula, subformula);
			    } /*end else*/
			} /*end else*/
			
			/*Add the var to the list so we don't use it again*/
			varNum = varList.addItem(search);
			local_root->num = varNum; /*record the variable number*/
			if (verbose == 1) {
			    fprintf(stderr, "adding item %s to varlist6\n", search.getName().c_str());
			} /*end if*/
			
			if (varOrder != 'z') {		    
			    /*Make self-loops at all vertices in the variable graph*/
			    connect_graph(varNum, varNum);
			} /*end if*/
		    } /*end if*/
		    else { /*variable already in varList*/
			varNum = ((KItem)(varList.find(search))).getInfo();
			local_root->num = varNum; /*record the variable number*/
			if (verbose) {
			    fprintf(stderr, "Avoiding5 redefinition of %s (var %d)\n", subformula, varNum);
			} /*end if*/
		    } /*end else*/
	    
		} /*end if(tgba)*/
		else { /*GBA, NOT TGBA*/
		    
		    if (smvFlag == 's') { /*SAL*/
			fprintf(SOUT, "       "); /*indent SAL module*/
			fprintf(SOUT, "S%s = ", subformula);
		    } /*end if*/
		    else {
			fprintf(SOUT, "S%s := ", subformula);
		    } /*end else*/
		    
		    printSubformula(formula_length, local_root->right_kid, SOUT);
		    fprintf(SOUT, " & (");
		    printSubformula(formula_length, local_root->left_kid, SOUT);
		    		    
		    if (smvFlag == 's') { /*SAL*/
			fprintf(SOUT, " OR EL_X%s);\n", subformula);
		    } /*end if*/
		    else { /*Cadence SMV or NuSMV*/
			fprintf(SOUT, " | EL_X%s);\n", subformula);
		    } /*end else*/
		    
		    /*Add the characteristic function to the list so we don't define it again*/
		    funcList.addItem(search);
		    if (verbose == 1) {
			fprintf(stderr, "adding item %s to funcList8\n", search.getName().c_str());
		    } /*end if*/
		    
		    if ( ! ( (local_root->parent != NULL) 
			     && (local_root->parent->me[0] == 'X') ) ) {
			/*Check if we've declared this variable yet*/
			sprintf(temp, "_X%s", subformula); /*NEW*/
			search.setName(temp);

			used = varList.query(search);
			if (used == 0) { /*we haven't used this variable name yet*/
			    
			    fprintf(OUT, "EL_X%s : boolean;\n", subformula); /*NEW*/
			    
			    /*Add a transition*/
			    if (Xcounter == 0) { 
				if (smvFlag == 's') { fprintf(TOUT, "       "); } /*indent SAL module*/
				fprintf(TOUT, "( EL");
			    } /*end if*/
			    else {
				if (smvFlag == 's') { fprintf(TOUT, "       "); } /*indent SAL module*/
				fprintf(TOUT, " &\n( EL");
			    } /*end else*/
			    Xcounter++;
			    
			    if (sloppy) {
				if (smvFlag == 's') { /*SAL*/
				    fprintf(TOUT, "_X%s -> (something') )", subformula);
				} /*end if*/
				else { /*Cadence SMV and NuSMV*/
				    /*fprintf(TOUT, "_X%s -> next(S%s) )", subformula, subformula);*/
				    fprintf(TOUT, "_X%s -> (next(", subformula);
				} /*end else*/
			    } /*end if*/
			    else {
				if (smvFlag == 's') { /*SAL*/
				    fprintf(TOUT, "_X%s = (something;) )", subformula);
				} /*end if*/
				else { /*Cadence SMV and NuSMV*/
				    fprintf(TOUT, "_X%s = (next(", subformula);
				} /*end else*/
			    } /*end else*/
			    getSubformulaVar(formula_length, local_root, temp);
			    fprintf(TOUT, "%s) ))", temp);
			    
			    /*Add the var to the list so we don't use it again*/
			    varNum = varList.addItem(search);
			    local_root->num = varNum; /*record the variable number*/
			    if (verbose == 1) {
				fprintf(stderr, "adding item %s to varlist6\n", search.getName().c_str());
			    } /*end if*/
			    
			    if (varOrder != 'z') {		    
				/*Make self-loops at all vertices in the variable graph*/
				connect_graph(varNum, varNum);
			    } /*end if*/
			} /*end if*/
			else { /*variable already in varList*/
			    varNum = ((KItem)(varList.find(search))).getInfo();
			    local_root->num = varNum; /*record the variable number*/
			    if (verbose) {
				fprintf(stderr, "Avoiding6 redefinition of %s (var %d)\n", subformula, varNum);
			    } /*end if*/
			} /*end else*/
		    } /*end if*/
		    
		} /*end else GBA*/
		break;
	    case 'G' :
		/*TGBA trees can now have "GF" operators -- check for those here*/
		if (tgba && (strcmp(local_root->me, "GF") == 0)) {
		    //fprintf(stderr, "\n\nGF!!!!!!\n\n");

		    /*Check if we've declared this variable yet*/
		    search.setName(subformula);
		    used = varList.query(search);
		    if (used == 0) { /*we haven't used this variable name yet*/
			/*if this if-statement is ever changed, the variable ordering connection must be changed*/

			if (smvFlag == 's') { /*SAL*/
			    fprintf(FOUT, "\n\n     fairness%d: THEOREM main |-  NOT P%s\n", 
				    fairnum, subformula);
			} /*end if SAL*/
			
			/*Cadence SMV or NuSMV*/
			else if (smvFlag == 'n') { /*NuSMV*/
			    fprintf(FOUT, "\nJUSTICE   (!P%s)\n", subformula);
			} /*end if*/
			else {/*Cadence SMV*/
			    /*Use promise var now*/
			    fprintf(FOUT, "\nFAIRNESS   (!P%s)\n", subformula, subformula);
			} /*end if Cadence SMV*/
			fairnum++;
			
			fprintf(OUT, "P%s: boolean;\n", subformula); /*promise variable*/
			if (define_P_vars) {
			    /*try defining the promise variable too*/
			    if (Xcounter > 0) {  fprintf(TOUT, " &\n"); }
			    Xcounter++;
			    fprintf(TOUT, "( P%s = (EL%s & (!", subformula, subformula);
			    printSubformula(formula_length, local_root->right_kid, TOUT);
			    fprintf(TOUT, ")) )"); /*end promise var definition*/
			} /*end if*/

			/*Add the var to the list so we can connect it into the var graph*/
			sprintf(temp, "%s%s", "P", subformula);
			search.setName(temp);
			promiseVarNum = varList.addItem(search);

			if (verbose == 1) {
			    fprintf(stderr, "G: adding item %s to varlist42\n", search.getName().c_str());
			} /*end if*/
			
			if (varOrder != 'z') {
			    /*Make self-loops at all vertices in the variable graph*/
			    connect_graph(promiseVarNum, promiseVarNum);
			} /*end if*/

		    } /*end if used*/
		    /*No else here b/c P-vars aren't connected to the rest of the tree*/
		    search.setName(subformula);

		    if ( ! ( varList.query(search) ) ) {/*we haven't been here before*/
			fprintf(OUT, "EL%s : boolean;\n", subformula);

			if (Xcounter == 0) { 
			    if (smvFlag == 's') { fprintf(TOUT, "       "); } /*indent SAL module*/
			    fprintf(TOUT, "( ");
			} /*end if*/
			else {
			    if (smvFlag == 's') { fprintf(TOUT, "       "); } /*indent SAL module*/
			    fprintf(TOUT, " &\n( ");
			} /*end else*/
			Xcounter++;
			
			if (sloppy) {
			    if (smvFlag == 's') { /*SAL*/
				fprintf(TOUT, "EL%s -> (S%s) )", subformula, subformula);
			    } /*end if*/
			    else { /*Cadence SMV and NuSMV*/
				fprintf(TOUT, "EL%s -> (S%s) )", subformula, subformula);
			    } /*end else*/
			} /*end if*/
			else {
			    if (smvFlag == 's') { /*SAL*/
				fprintf(TOUT, "EL%s = (S%s) )", subformula, subformula);
			    } /*end if*/
			    else { /*Cadence SMV and NuSMV*/
				fprintf(TOUT, "EL%s = (S%s) )", subformula, subformula);
			    } /*end else*/
			} /*end else*/
			
			/*Add the var to the list so we don't use it again*/
			varNum = varList.addItem(search);
			local_root->num = varNum; /*record the variable number*/
			if (verbose == 1) {
			    fprintf(stderr, "G: adding item %s to varlist42\n", search.getName().c_str());
			} /*end if*/
			
			if (varOrder != 'z') {
			    /*Make self-loops at all vertices in the variable graph*/
			    connect_graph(varNum, varNum);
			    connect_graph(varNum, promiseVarNum);
			} /*end if*/
			
			if (smvFlag == 's') { /*SAL*/
			    fprintf(SOUT, "       "); /*indent SAL module*/
			    fprintf(SOUT, "S%s = ((next(EL%s)) AND ((", subformula, subformula);
			} /*end if*/
			else {
			    fprintf(SOUT, "S%s := ((next(EL%s)) & ((", subformula, subformula);
			} /*end else*/

			printSubformula(formula_length, local_root->right_kid, SOUT);

			if (smvFlag == 's') { /*SAL*/
			    fprintf(SOUT, ") OR (P%s)));\n", subformula);
			} /*end if*/
			else { /*Cadence SMV or NuSMV*/
			    fprintf(SOUT, ") | (P%s)));\n", subformula); 
			} /*end else*/

			/*Add the characteristic function to the list so we don't define it again*/
			funcList.addItem(search);
			if (verbose == 1){
			    fprintf(stderr, "adding item %s to funcList6\n", search.getName().c_str());
			} /*end if*/
			
		    } /*end if*/
		    else { /*variable already in varList*/
			varNum = ((KItem)(varList.find(search))).getInfo();
			local_root->num = varNum; /*record the variable number*/
			if (verbose) {
			    fprintf(stderr, "Avoiding32 redefinition of %s (var %d)\n", subformula, varNum);
			} /*end if*/
		    } /*end else*/

		    break;
		} /*end if GF*/

		if (tgba) {
		    /*Check if we've declared this variable yet*/
		    search.setName(subformula);
		    used = varList.query(search);
		    //fprintf(stderr, "Looking at subformula: %s; here = %d\n", temp, used);
		    if (used == 0) { /*we haven't used this variable name yet*/
			/*if this if-statement is ever changed, the variable ordering connection must be changed*/
			
			if (smvFlag == 's') { /*SAL*/
			    fprintf(SOUT, "       "); /*indent SAL module*/
			    fprintf(SOUT, "S%s = ", subformula);
			} /*end if*/
			else {
			    fprintf(SOUT, "S%s := ", subformula);
			} /*end else*/
			
			printSubformula(formula_length, local_root->right_kid, SOUT);

			if (smvFlag == 's') { /*SAL*/
			    fprintf(SOUT, " AND (next(EL%s));\n", subformula);
			} /*end if*/
			else { /*Cadence SMV or NuSMV*/
			    fprintf(SOUT, " & (next(EL%s));\n", subformula); 
			} /*end else*/

			/*Add the characteristic function to the list so we don't define it again*/
			funcList.addItem(search);
			if (verbose == 1) {
			    fprintf(stderr, "adding item %s to funcList8\n", search.getName().c_str());
			} /*end if*/
		    } /*end if*/

		    search.setName(subformula);
		    if ( ! ( varList.query(search) ) ) {/*we haven't been here before*/

			fprintf(OUT, "EL%s : boolean;\n", subformula); /*NEW*/
			
			if (Xcounter == 0) { 
			    if (smvFlag == 's') { fprintf(TOUT, "       "); } /*indent SAL module*/
			    fprintf(TOUT, "( EL");
			} /*end if*/
			else {
			    if (smvFlag == 's') { fprintf(TOUT, "       "); } /*indent SAL module*/
			    fprintf(TOUT, " &\n( EL");
			} /*end else*/
			Xcounter++;
			
			if (sloppy) {
			    if (smvFlag == 's') { /*SAL*/
				fprintf(TOUT, "%s -> (S%s) )", subformula, subformula);
			    } /*end if*/
			    else { /*Cadence SMV and NuSMV*/
				fprintf(TOUT, "%s -> (S%s) )", subformula, subformula);
			    } /*end else*/
			} /*end if*/
			else {
			    if (smvFlag == 's') { /*SAL*/
				fprintf(TOUT, "%s = (S%s) )", subformula, subformula);
			    } /*end if*/
			    else { /*Cadence SMV and NuSMV*/
				fprintf(TOUT, "%s = (S%s) )", subformula, subformula);
			    } /*end else*/
			} /*end else*/
			
			/*Add the var to the list so we don't use it again*/
			varNum = varList.addItem(search);
			local_root->num = varNum; /*record the variable number*/
			if (verbose == 1) {
			    fprintf(stderr, "adding item %s to varlist6\n", search.getName().c_str());
			} /*end if*/
			
			if (varOrder != 'z') {		    
			    /*Make self-loops at all vertices in the variable graph*/
			    //fprintf(stderr, "connect8\n");
			    connect_graph(varNum, varNum);
			    /*fprintf(stderr, "Connecting3 var %d to var %d\n", varNum, varNum);*/
			} /*end if*/
		    } /*end if*/
		    else { /*variable already in varList*/
			varNum = ((KItem)(varList.find(search))).getInfo();
			local_root->num = varNum; /*record the variable number*/
			if (verbose) {
			    fprintf(stderr, "Avoiding5 redefinition of %s (var %d)\n", subformula, varNum);
			} /*end if*/
		    } /*end else*/

		    break;
		} /*end if tgba*/
		else { /*GBA, NOT TGBA*/
		    if (smvFlag == 's') { /*SAL*/
			fprintf(SOUT, "       "); /*indent SAL module*/
			fprintf(SOUT, "S%s = ", subformula, temp, subformula);
		    } /*end if*/
		    else { /*Cadence SMV or NuSMV*/
			fprintf(SOUT, "S%s := ", subformula, temp, subformula);
		    } /*end else*/
		    
		    printSubformula(formula_length, local_root->right_kid, SOUT);
		    
		    if (smvFlag == 's') { /*SAL*/
			fprintf(SOUT, " AND EL_X%s;\n", subformula);
		    } /*end if*/
		    else { /*Cadence SMV or NuSMV*/
			fprintf(SOUT, " & EL_X%s;\n", subformula); 
		    } /*end else*/
		   		    		    
		    /*Add the characteristic function to the list so we don't define it again*/
		    funcList.addItem(search);
		    if (verbose == 1) {
			fprintf(stderr, "adding item %s to funcList10\n", search.getName().c_str());
		    } /*end if*/
		    
		    if ( ! ( (local_root->parent != NULL) 
			     && (local_root->parent->me[0] == 'X') ) ) {
			/*Check if we've declared this variable yet*/
			sprintf(temp, "_X%s", subformula); /*NEW*/
			search.setName(temp);
			
			used = varList.query(search);
			if (used == 0) { /*we haven't used this variable name yet*/
			    
			    fprintf(OUT, "EL_X%s : boolean;\n", subformula); /*NEW*/
			    
			    /*Add a transition*/
			    if (Xcounter == 0) { 
				if (smvFlag == 's') { fprintf(TOUT, "       "); } /*indent SAL module*/
				fprintf(TOUT, "( EL");
			    } /*end if*/
			    else {
				if (smvFlag == 's') { fprintf(TOUT, "       "); } /*indent SAL module*/
				fprintf(TOUT, " &\n( EL");
			    } /*end else*/
			    Xcounter++;
			    
			    if (sloppy) {
				if (smvFlag == 's') { /*SAL*/
				    fprintf(TOUT, "_X%s -> (something') )", subformula);
				} /*end if*/
				else { /*Cadence SMV and NuSMV*/
				    /*fprintf(TOUT, "_X%s -> next(S%s) )", subformula, subformula);*/
				    fprintf(TOUT, "_X%s -> (next(", subformula);
				} /*end else*/
			    } /*end if*/
			    else {
				if (smvFlag == 's') { /*SAL*/
				    fprintf(TOUT, "_X%s = (something;) )", subformula);
				} /*end if*/
				else { /*Cadence SMV and NuSMV*/
				    fprintf(TOUT, "_X%s = (next(", subformula);
				} /*end else*/
			    } /*end else*/
			    getSubformulaVar(formula_length, local_root, temp);
			    fprintf(TOUT, "%s) ))", temp);
			    
			    /*Add the var to the list so we don't use it again*/
			    varNum = varList.addItem(search);
			    local_root->num = varNum; /*record the variable number*/
			    if (verbose == 1) {
				fprintf(stderr, "adding item %s to varlist8\n", search.getName().c_str());
			    } /*end if*/
			    
			    if (varOrder != 'z') {
				/*Make self-loops at all vertices in the variable graph*/
				//fprintf(stderr, "connect11\n");
				connect_graph(varNum, varNum);
				/*fprintf(stderr, "Connecting4 var %d to var %d\n", varNum, varNum);*/
			    } /*end if*/
			} /*end if*/
			else { /*variable already in varList*/
			    if (verbose) {
				fprintf(stderr, "Avoiding1 redefinition of %s\n", subformula);
			    } /*end if*/
			    varNum = ((KItem)(varList.find(search))).getInfo();
			    local_root->num = varNum; /*record the variable number*/
			} /*end else*/
		    } /*end if*/
		    break;		    
		} /*end else gba*/

	    case 'F' :
		if (tgba) { /*P-vars*/
		    /*Check if we've declared this variable yet*/
		    search.setName(subformula);
		    used = varList.query(search);
		    /*fprintf(stderr, "Looking at subformula: %s\n", temp);*/
		    if (used == 0) { /*we haven't used this variable name yet*/
			/*if this if-statement is ever changed, the variable ordering connection must be changed*/
			
			if (smvFlag == 's') { /*SAL*/
			    /*fprintf(FOUT, "\n\n     fairness%d: THEOREM main |-  NOT EL%s OR S%s\n", 
			      fairnum, subformula, temp); /*Use promise var now*/
			    fprintf(FOUT, "\n\n     fairness%d: THEOREM main |-  NOT P%s\n", 
				    fairnum, subformula);
			} /*end if SAL*/
			
			/*Cadence SMV or NuSMV*/
			else if (smvFlag == 'n') { /*NuSMV*/
			    /*fprintf(FOUT, "\nJUSTICE   (!EL%s | ", subformula); /*Use promise var now*/
			    fprintf(FOUT, "\nJUSTICE   (!P%s)\n", subformula);
			} /*end if*/
			else {/*Cadence SMV*/
			    /*fprintf(FOUT, "\nFAIRNESS   (!EL%s | ", subformula);*/
			    /*Use promise var now*/
			    fprintf(FOUT, "\nFAIRNESS   (!P%s)\n", subformula, subformula);
			} /*end if Cadence SMV*/
			fairnum++;
			
			fprintf(OUT, "P%s: boolean;\n", subformula); /*promise variable*/
			if (define_P_vars) {
			    /*try defining the promise variable too*/
			    if (Xcounter > 0) {  fprintf(TOUT, " &\n"); }
			    Xcounter++;
			    fprintf(TOUT, "( P%s = (EL%s & (!", subformula, subformula);
			    printSubformula(formula_length, local_root->right_kid, TOUT);
			    fprintf(TOUT, ")) )"); /*end promise var definition*/
			} /*end if*/

			/*Add the var to the list so we can connect it into the var graph*/
			sprintf(temp, "%s%s", "P", subformula);
			search.setName(temp);
			promiseVarNum = varList.addItem(search);
			if (verbose == 1) {
			    fprintf(stderr, "F: adding item %s to varlist44\n", search.getName().c_str());
			} /*end if*/
			
			if (varOrder != 'z') {
			    /*Make self-loops at all vertices in the variable graph*/
			    connect_graph(promiseVarNum, promiseVarNum);
			} /*end if*/

		    } /*end if used*/
		    /*No else here b/c P-vars aren't connected to the rest of the tree*/
		    search.setName(subformula);
		    if ( ! ( varList.query(search) ) ) {/*we haven't been here before*/
			fprintf(OUT, "EL%s : boolean;\n", subformula);
			
			if (Xcounter == 0) { 
			    if (smvFlag == 's') { fprintf(TOUT, "       "); } /*indent SAL module*/
			    fprintf(TOUT, "( ");
			} /*end if*/
			else {
			    if (smvFlag == 's') { fprintf(TOUT, "       "); } /*indent SAL module*/
			    fprintf(TOUT, " &\n( ");
			} /*end else*/
			Xcounter++;
			
			if (sloppy) {
			    if (smvFlag == 's') { /*SAL*/
				fprintf(TOUT, "EL%s -> (S%s) )", subformula, subformula);
			    } /*end if*/
			    else { /*Cadence SMV and NuSMV*/
				fprintf(TOUT, "EL%s -> (S%s) )", subformula, subformula);
			    } /*end else*/
			} /*end if*/
			else {
			    if (smvFlag == 's') { /*SAL*/
				fprintf(TOUT, "EL%s = (S%s) )", subformula, subformula);
			    } /*end if*/
			    else { /*Cadence SMV and NuSMV*/
				fprintf(TOUT, "EL%s = (S%s) )", subformula, subformula);
			    } /*end else*/
			} /*end else*/
			
			/*Add the var to the list so we don't use it again*/
			varNum = varList.addItem(search);
			local_root->num = varNum; /*record the variable number*/
			if (verbose == 1) {
			    fprintf(stderr, "F: adding item %s to varlist45\n", search.getName().c_str());
			} /*end if*/
			//fprintf(stderr, "F: adding item %s to varlist as var #%d\n", search.getName().c_str(), varNum);
			if (varOrder != 'z') {
			    /*Make self-loops at all vertices in the variable graph*/
			    //fprintf(stderr, "connect6\n");
			    connect_graph(varNum, varNum);
			    /*fprintf(stderr, "Connecting1 var %d to var %d\n", varNum, varNum);*/
			    //fprintf(stderr, "connect21\n");
			    connect_graph(varNum, promiseVarNum);
			} /*end if*/
			

			if (smvFlag == 's') { /*SAL*/
			    fprintf(SOUT, "       "); /*indent SAL module*/
			    fprintf(SOUT, "S%s = ( (", subformula);
			} /*end if*/
			else {
			    fprintf(SOUT, "S%s := ( (", subformula);
			} /*end else*/

			printSubformula(formula_length, local_root->right_kid, SOUT);
			if (smvFlag == 's') { fprintf(SOUT, ") OR ("); } /*SAL*/
			else { fprintf(SOUT, ") | ("); }                 /*not SAL*/
			if (smvFlag == 's') { /*SAL*/
			    /*changed for resolution*/
			    /*fprintf(SOUT, "%s AND S_X%s);\n", temp, subformula);*/
			    fprintf(SOUT, "P%s AND (next(EL%s))));\n", subformula, subformula);
			} /*end if SAL*/
			else { /*Cadence SMV or NuSMV*/
			    /*changed for resolution*/
			    /*fprintf(SOUT, "%s & S_X%s);\n", temp, subformula);*/
			    /*resolution:out fprintf(SOUT, "%s & EL_X%s);\n", temp, subformula);*/
			    fprintf(SOUT, "P%s & (next(EL%s))));\n", subformula, subformula);
			} /*end else*/

			/*Add the characteristic function to the list so we don't define it again*/
			funcList.addItem(search);
			if (verbose == 1){
			    fprintf(stderr, "adding item %s to funcList6\n", search.getName().c_str());
			} /*end if*/
			
		    } /*end if*/
		    else { /*variable already in varList*/
			varNum = ((KItem)(varList.find(search))).getInfo();
			local_root->num = varNum; /*record the variable number*/
			if (verbose) {
			    fprintf(stderr, "Avoiding8 redefinition of %s (var %d)\n", subformula, varNum);
			} /*end if*/
			
		    } /*end else*/		    
		} /*end if(tgba)*/
		else { /*GBA, NOT TGBA*/

		    if (smvFlag == 's') { /*SAL*/
			fprintf(FOUT, "\n\n     fairness%d: THEOREM main |-  NOT S%s OR ", 
				fairnum, subformula);
			    printSubformula(formula_length, local_root->right_kid, FOUT);
			    fprintf(FOUT, "\n");
			fprintf(SOUT, "       "); /*indent SAL module*/
			/*changed for resolution*/
			/*fprintf(SOUT, "S%s = S%s OR S_X%s;\n", subformula, temp, subformula);*/
			fprintf(SOUT, "S%s = ", subformula);
		    } /*end if SAL*/
		    else { /*Cadence SMV or NuSMV*/
			if (smvFlag == 'n') { /*NuSMV*/
			    fprintf(FOUT, "\nJUSTICE   (!S%s | ", subformula);
			    printSubformula(formula_length, local_root->right_kid, FOUT);
			    fprintf(FOUT, ")\n");
			} /*end if*/
			else {/*Cadence SMV*/
			    fprintf(FOUT, "\nFAIRNESS   (!S%s | ", subformula);
			    printSubformula(formula_length, local_root->right_kid, FOUT);
			    fprintf(FOUT, ")\n");
			} /*end else*/
						
			fprintf(SOUT, "S%s := ", subformula);
		    } /*end else*/
		    
		    printSubformula(formula_length, local_root->right_kid, SOUT);
		    fairnum++; /*we just added another fairness statement*/
		    
		    if (smvFlag == 's') { /*SAL*/
			fprintf(SOUT, " OR EL_X%s;\n", subformula);
		    } /*end if*/
		    else { /*Cadence SMV or NuSMV*/
			fprintf(SOUT, " | EL_X%s;\n", subformula); 
		    } /*end else*/
		    
		    
		    /*Add the characteristic function to the list so we don't define it again*/
		    funcList.addItem(search);
		    if (verbose == 1) {
			fprintf(stderr, "adding item %s to funcList11\n", search.getName().c_str());
		    } /*end if*/
		} /*end else gba*/
		
		if ( (tgba == 0) && ( ! ( (local_root->parent != NULL) 
					  && (local_root->parent->me[0] == 'X') ) ) ) {
		    /*Check if we've declared this variable yet*/
		    /*sprintf(temp, "S_X%s", subformula); OLD*/
		    sprintf(temp, "_X%s", subformula); /*NEW*/
		    search.setName(temp);
		    used = varList.query(search);
		    if (verbose) {fprintf(stderr, "F: Looking at subformula: %s\n", temp);}
		    if (used == 0) { /*we haven't used this variable name yet*/
			
			fprintf(OUT, "EL_X%s : boolean;\n", subformula); /*NEW*/
			
			/*Add a transition*/
			if (Xcounter == 0) { 
			    if (smvFlag == 's') { fprintf(TOUT, "       "); } /*indent SAL module*/
			    fprintf(TOUT, "( EL");
			} /*end if*/
			else {
			    if (smvFlag == 's') { fprintf(TOUT, "       "); } /*indent SAL module*/
			    fprintf(TOUT, " &\n( EL");
			} /*end else*/
			Xcounter++;
			
			if (sloppy) {
			    if (smvFlag == 's') { /*SAL*/
				fprintf(TOUT, "_X%s -> (something') )", subformula);
			    } /*end if*/
			    else { /*Cadence SMV and NuSMV*/
				/*fprintf(TOUT, "_X%s -> next(S%s) )", subformula, subformula);*/
				fprintf(TOUT, "_X%s -> (next(", subformula);
			    } /*end else*/
			} /*end if*/
			else {
			    if (smvFlag == 's') { /*SAL*/
				fprintf(TOUT, "_X%s = (something;) )", subformula);
			    } /*end if*/
			    else { /*Cadence SMV and NuSMV*/
				/*fprintf(TOUT, "_X%s = next(S%s) )", subformula, subformula);*/
				fprintf(TOUT, "_X%s = (next(", subformula);
			    } /*end else*/
			} /*end else*/
			getSubformulaVar(formula_length, local_root, temp);
			/*printSubformula(formula_length, local_root, TOUT); wrong*/
			fprintf(TOUT, "%s) ))", temp);
		    
			/*Add the var to the list so we don't use it again*/
			varNum = varList.addItem(search);
			local_root->num = varNum; /*record the variable number*/
			if (verbose == 1) {
			    fprintf(stderr, "adding item %s to varlist9\n", search.getName().c_str());
			} /*end if*/

			if (varOrder != 'z') {
			    /*Make self-loops at all vertices in the variable graph*/
			    //fprintf(stderr, "connect13\n");
			    connect_graph(varNum, varNum);
			    /*fprintf(stderr, "Connecting4 var %d to var %d\n", varNum, varNum);*/
			} /*end if*/
		    } /*end if*/
		    else { /*variable already in varList*/
			if (verbose) {
			    fprintf(stderr, "Avoiding1 redefinition of %s\n", subformula);
			} /*end if*/
			varNum = ((KItem)(varList.find(search))).getInfo();
			local_root->num = varNum; /*record the variable number*/
		    } /*end else*/		    
		} /*end if*/
		break;
	    default : 
		fprintf(stderr, "ERROR2: Unrecognized parsed operator \'%c\'\n", local_root->me[0]);
		exit(1);
	} /*end switch*/
    } /*end if*/
    else {
	if ( varList.query(search) ) {
	    varNum = ((KItem)(varList.find(search))).getInfo();
	    local_root->num = varNum; /*record the variable number*/
	    if (verbose) {
		fprintf(stderr, "Avoiding9 redefinition of %s (var %d)\n", subformula, varNum);
	    } /*end if*/
	} /*end if*/
	if (verbose) {
	    fprintf(stderr, "Avoiding99 redefinition of %s (var %d)\n", subformula, local_root->num);
	    fprintf(stderr, "varlist query is %d and funclist query is %d\n", varList.query(search), funcList.query(search));
	} /*end if*/
    } /*end else*/

    if (verbose) {
	fprintf(stderr, "compiled subformula: %s\n", subformula);
	fprintf(stderr, "rootPtr = %d\n", rootPtr);
	fprintf(stderr, "local root %c is at position %d\n", subformula[rootPtr], rootPtr);
    } /*end if*/
    
    /*Clean up memory*/
    if (subformula != NULL) {
	if (verbose) {
	    fprintf(stderr, "Freeing subformula\n");
	} /*end if*/
	free(subformula);
	} /*end if*/
    if (temp != NULL) {
	if (verbose) {
	    fprintf(stderr, "Freeing temp\n");
	} /*end if*/
	free(temp);
    } /*end if*/
    //return varNum;
    return local_root->num; 
} /*end printSubformulaVar_makeGraph*/



/* Function printFormulaVar
   Purpose: print the whole subformula rooted to the
      output file, using _'s instead of ()'s so as to make the
      subformula into a variable name. 

   No fancy stuff like printSubformulaVar.

   Note: this could be written to use less memory by only storing the last
      string of ___'s and then printing them whenever a non-_ is printed.
      That would avoid trailing ___'s on the variable name.
*/
void printFormulaVar() {
    struct node *current = root;
    char *formula;         /*the string representing the subformula*/
    short visited_left=0, visited_right=0;
    int i;

    /*fprintf(stderr, "printFormulaVar here\n");*/

    /*Error Check*/
    if((formula_length == 0) || (root == NULL)) {
	fprintf(stderr, "Warning: Can't print an empty formula\n");
	return;
    } /*end if*/

    formula = (char *)malloc(sizeof(char) * ((formula_length*2)+1));
    if (formula == NULL){ fprintf(stderr, "Memory error4\n"); exit(1); }
    strcpy(formula, "\0"); /*make sure subformula starts empty*/
    /*fprintf(stderr, "3333formula so far: %s\n", formula);*/

    if ((root->right_kid == NULL) && (root->left_kid == NULL)) {
	/*leaf*/
	strcpy(formula, root->me);
	if (verbose) {
	    fprintf(stderr, "Formula is a leaf: %s\nFormula is now: %s", root->me, formula);
	} /*end if*/

	fprintf(OUT, "%s", formula);
	
	/*Clean up memory*/
	if (formula != NULL) {
	    if (verbose) {
		fprintf(stderr, "2Freeing formula\n");
	    } /*end if*/
	    free(formula);
	} /*end if*/
	
	return;
    } /*end if*/
    
    /*Loop while we haven't reached the root 
      after exploring it's right branch*/
    sprintf(formula, "%s_", formula);
    /*fprintf(stderr, "4formula so far: %s\n", formula);*/
    while (! ((current == root) && (visited_right == 1)) ) {
	
	if (visited_left == 1) {
	    visited_left = 0;
	} /*end if*/
	else {
	    if (current->left_kid != NULL) {
		current = current->left_kid;
		sprintf(formula, "%s_", formula);
		/*fprintf(stderr, "5formula so far: %s\n", formula);*/
		continue;
	    } /*end if*/
	} /*end else*/

	if (visited_right == 1) {
	    visited_right = 0;
	} /*end if*/
	else {
	    if (current->me[0] == '~') {
		sprintf(formula, "%s%s", formula, "NOT");
	    } /*end if*/
	    else if (current->me[0] == '&') {
		sprintf(formula, "%s%s", formula, "AND");
	    } /*end if*/
	    else if (current->me[0] == '|') {
		sprintf(formula, "%s%s", formula, "OR");
	    } /*end if*/
	    else if ((current->me[0] == '-')
		     || (current->me[0] == '>')) {
		sprintf(formula, "%s%s", formula, "IMP");
	    } /*end if*/
	    else { /*just put in current->me as part of the variable name*/
		sprintf(formula, "%s%s", formula, current->me);
	    } /*end else*/
	    /*fprintf(stderr, "6formula so far: %s\n", formula);*/
	    if (current->right_kid != NULL) {
		current = current->right_kid;
		sprintf(formula, "%s_", formula);
		/*fprintf(stderr, "7formula so far: %s\n", formula);*/
		continue;
	    } /*end if*/
	    else {
		if (current == root) {
		    visited_right = 1;
		} /*end if*/
	    } /*end else*/
	} /*end else*/

	if (current->parent != NULL) {
	    visited_left = 1;
	    sprintf(formula, "%s_", formula);
	    /*fprintf(stderr, "8formula so far: %s\n", formula);*/
	    if (current->parent->right_kid == current) {
		visited_right = 1;
	    } /*end if*/
	    current = current->parent;
	} /*end if*/
	
    } /*end while*/

    /*Remove trailing '_'s from the formula*/
    i = strlen(formula) - 1;
    while( (i > 0) && (formula[i] == '_')) {
	formula[i] = '\0';
	i--;
    } /*end while*/
    
    if ((tgba) || ((!tgba) && (root->me[0] == 'X'))) {
	fprintf(OUT, "EL%s", formula);
    } /*end if*/
    else {
	fprintf(OUT, "S%s", formula);
    } /*end else*/

    /*Clean up memory*/
    if (formula != NULL) {
	if (verbose) {
	    fprintf(stderr, "3Freeing formula\n");
	} /*end if*/
	free(formula);
    } /*end if*/
    
    return;
} /*end printFormulaVar*/


/* Function boolNormalForm
In one pre-order traversal, transforms the formula into BNF and reduces the operators.
    Purposes:
      (1) eliminates operators '&,' '->,' 'R,' and 'G' from the formula
      (2) eliminates double negations
      (3) for TGBA: combines GF into one operator (proposed)
*/
void boolNormalForm() {
    struct node *current = root;
    struct node *temp;
    int i = 0;
    short visited_left=0, visited_right=0;

    /*Error Check*/
    if((formula_length == 0) || (current == NULL)) {
	fprintf(stderr, "Warning: Can't reduce an empty formula\n");
	return;
    } /*end if*/
 
    if (verbose) {
	fprintf(stderr, "---------------------------\nboolNormalForm: REDUCING OPERATORS\n");
    } /*end if*/
    
    /*Loop while we haven't reached the root 
      after exploring it's right branch*/
    while (! ((current == root) && (visited_right == 1)) ) {

	if ((visited_left == 0)
	    && (visited_right == 0)) {
	    
            /*Visit this node*/
	    
	    /*Check this node of the formula*/
	    if (verbose) {
	      /*printFormula(formula_length);*/
		fprintf(stderr, "1currently examining: %s\n", current->me);
		if (root -> parent != NULL) {
		    fprintf(stderr, "ERROR2: root->parent != NULL\n");
		} /*end if*/
	    } /*end if*/
	    switch (current->me[0]) {
		case '-' :
		case '>' : /*(a -> b) becomes ((~a) | b)*/
		    current->me[0] = '|';
		    current->me[1] = '\0'; /*make sure to end the string*/
		    
		    /*This node could have temp_kid set because of left_kid; check*/
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

		    negate(current->left_kid);
		    
		    /*Adjust the formula length*/
		    /*formula_length++;*/

		    break;
		    
		case '&' : /*(a & b) becomes ~(~a | ~b)*/
		    negate(current);
		    current->me[0] = '|';
		    current->temp_kid = 0; /*both kids are now ~*/
		    negate(current->left_kid);
		    negate(current->right_kid);

		    /*Adjust the formula length*/
		    formula_length += 6;

		    /*Travel up to the new preceeding negation to process that node*/
		    if (current != root) {current = current->parent;}
                    /*Process double negations*/
		    if ((current->parent != NULL) && (current->parent->me[0] == '~')) {
			current = current->parent;
		    } /*end if*/

		    break;

		case 'R' : /*(a R b) becomes ~(~a U ~b)*/

		  if (strcmp(current->me, "R") != 0) { 
		    /*don't change props starting with this letter*/
		    break;
		  } /*end if*/

		    negate(current);
		    current->me[0] = 'U';
		    current->temp_kid = 0; /*both kids are now ~*/
		    negate(current->left_kid);
		    negate(current->right_kid);

		    /*Adjust the formula length*/
		    formula_length += 6;

		    /*Travel up to the new preceeding negation to process that node*/
		    if (current != root) {current = current->parent;}
		    /*Process double negations*/
		    if ((current->parent != NULL) && (current->parent->me[0] == '~')) {
			current = current->parent;
		    } /*end if*/

		    break;

		case 'G' : /*(G a) becomes ~(F ~a)*/

		  if (strcmp(current->me, "G") != 0) { 
		    /*don't change props starting with this letter*/
		    break;
		  } /*end if*/

		    negate(current);
		    current->me[0] = 'F';
		    current->temp_kid = 0; /*kid is now ~*/
		    negate(current->right_kid);

		    /*Adjust the formula length*/
		    formula_length += 4;
		    
		    /*Travel up to the new preceeding negation to process that node*/
		    if (current != root) {current = current->parent;}
		    /*Process double negations*/
		    if ((current->parent != NULL) && (current->parent->me[0] == '~')) {
			current = current->parent;
		    } /*end if*/

		    break;
		    
		default : 
		    /*This doesn't work if there's any default statement here*/
		    break;
	    } /*end switch*/
	    if (verbose) {
		fprintf(stderr, "checking for ~~\n");
	    } /*end if*/
	    /*Second check: eliminate double negations caused by this check*/
	    switch(current->me[0]) {
		case '~' : 
		    if (current->right_kid == NULL) {
			fprintf(stderr, "ERROR: Negation with no right child!\n");
			exit(1);
		    } /*end if*/
		    
		    switch (current->right_kid->me[0]) {
			
			case '~' : /*(~~a) becomes a*/
			    /*We have a double negation*/
			    
			    if (current->parent == NULL) {
				/*We're at the root*/
				
				/*error checking*/
				if (root != current) {
				    fprintf(stderr, "ERROR: non-root node with NULL parent!\n");
				    exit(1);
				} /*end if*/
				
				/*reset the root*/
				root = current->right_kid->right_kid;
				if (root == NULL) {
				    fprintf(stderr, "ERROR: Negation with no right child!\n");
				    exit(1);
				} /*end if*/
				root->parent = NULL;
			    } /*end if*/
			    else { /*We're not at the root*/
				if (current->parent->left_kid == current) {
				    current->parent->left_kid = current->right_kid->right_kid;
				} /*end if*/
				else { /*current is the right kid*/
				    current->parent->right_kid = current->right_kid->right_kid;
				} /*end else*/
				
				if (current->right_kid->right_kid != NULL) {
				    current->right_kid->right_kid->parent = current->parent;

				    /*Check for new temp_kid*/
				    if ((current->right_kid->right_kid->me[0] == 'X')
					|| (current->right_kid->right_kid->me[0] == 'U')
					|| (current->right_kid->right_kid->me[0] == 'R')
					|| (current->right_kid->right_kid->me[0] == 'F')
					|| (current->right_kid->right_kid->me[0] == 'G')) {
					current->parent->temp_kid = 1;
				    } /*end if*/
				    /*else, temporal setting from other kid of parent reigns*/

				} /*end if*/
			    } /*end else*/
			    
			    /*delete the first negation*/
			    temp = current;
			    current = current->right_kid;
			    free (temp->me);
			    free (temp);
			    
			    /*delete the second negation*/
			    free (current->me);
			    free (current);
			    
			    /*Adjust the formula length*/
			    formula_length -= 4; /*2 per ~ operator*/
			    
			    break;
		    } /*end switch*/
		    break;
	    } /*end switch*/
	} /*end if*/
	
	if ((current->left_kid != NULL)
	    && (visited_left == 0)) {
		current = current->left_kid;
		/*sprintf(formula, "%s(", formula);*/
		continue;
	} /*end if*/
	
	else if ((current->right_kid != NULL)
		 && (visited_right == 0)) {
	    current = current->right_kid;
	    visited_left = 0;
	    visited_right = 0;
	    continue;
	} /*end else if*/
	else {
	    if (current->parent == NULL) {
		if (current != root) {
		    fprintf(stderr, "ERROR1: malformed parse tree detected in preorder traversal\n");
		    exit(1);
		} /*end if*/
		else { /*formula of length 1*/
		    visited_right = 1;
		    continue;
		} /*end else*/
	    } /*end if*/
	    
	    
	    if (current->parent->right_kid == current) {
		visited_right = 1;
	    } /*end if*/
	    else {
		visited_right = 0;
	    } /*end else*/
	    current = current->parent;
	    visited_left = 1;
	} /*end else*/
    } /*end while*/		
    
    return;
} /*end boolNormalForm*/


/* Function NoRForm
In one pre-order traversal, transforms the formula to eliminate the R-operator for tools which can't parse it.
    Purposes:
      (1) eliminates operators 'R' from the formula
      (2) eliminates double negations
*/
void NoRForm() {
    struct node *current = root;
    struct node *temp;
    int i = 0;
    short visited_left=0, visited_right=0;

    /*Error Check*/
    if((formula_length == 0) || (current == NULL)) {
	fprintf(stderr, "Warning: Can't reduce an empty formula\n");
	return;
    } /*end if*/
 
    if (verbose) {
	fprintf(stderr, "---------------------------\nboolNormalForm: REDUCING OPERATORS\n");
    } /*end if*/
    
    /*if (current == root) {
	fprintf(stderr, "starting current as root...\n");
    }
    if (root->visited_right == 1) {
	fprintf(stderr, "root right kid visited...\n");
    }
    else if (root->visited_right == 0){
	fprintf(stderr, "root right kid unvisited...\n");
    }
    else {
	fprintf(stderr, "error: root->visited_right is %d\n", root->visited_right);
	}*/
    
    /*Loop while we haven't reached the root 
      after exploring it's right branch*/
    while (! ((current == root) && (visited_right == 1)) ) {

	if ((visited_left == 0)
	    && (visited_right == 0)) {
	    
            /*Visit this node*/
	    
	    /*Check this node of the formula*/
	    if (verbose) {
	      /*printFormula(formula_length);*/
		fprintf(stderr, "2currently examining: %s\n", current->me);
		if (root -> parent != NULL) {
		    fprintf(stderr, "ERROR2: root->parent != NULL\n");
		} /*end if*/
	    } /*end if*/
	    switch (current->me[0]) {
		case 'R' : /*(a R b) becomes ~(~a U ~b)*/

		  if (strcmp(current->me, "R") != 0) { 
		    /*don't change props starting with this letter*/
		    break;
		  } /*end if*/
		  
		    negate(current);
		    current->me[0] = 'U';
		    current->temp_kid = 0; /*both kids are now ~*/
		    negate(current->left_kid);
		    negate(current->right_kid);

		    /*Adjust the formula length*/
		    formula_length += 6;

		    /*Travel up to the new preceeding negation to process that node*/
		    if (current != root) {current = current->parent;}
		    /*Process double negations*/
		    if ((current->parent != NULL) && (current->parent->me[0] == '~')) {
			current = current->parent;
		    } /*end if*/

		    break;
		    
		default : 
		    /*This doesn't work if there's any default statement here*/
		    break;
	    } /*end switch*/
	    if (verbose) {
		fprintf(stderr, "checking for ~~\n");
	    } /*end if*/
	    /*Second check: eliminate double negations caused by this check*/
	    switch(current->me[0]) {
		case '~' : 
		    if (current->right_kid == NULL) {
			fprintf(stderr, "ERROR: Negation with no right child!\n");
			exit(1);
		    } /*end if*/
		    
		    switch (current->right_kid->me[0]) {
			
			case '~' : /*(~~a) becomes a*/
			    /*We have a double negation*/
			    
			    if (current->parent == NULL) {
				/*We're at the root*/
				
				/*error checking*/
				if (root != current) {
				    fprintf(stderr, "ERROR: non-root node with NULL parent!\n");
				    exit(1);
				} /*end if*/
				
				/*reset the root*/
				root = current->right_kid->right_kid;
				if (root == NULL) {
				    fprintf(stderr, "ERROR: Negation with no right child!\n");
				    exit(1);
				} /*end if*/
				root->parent = NULL;
			    } /*end if*/
			    else { /*We're not at the root*/
				if (current->parent->left_kid == current) {
				    current->parent->left_kid = current->right_kid->right_kid;
				} /*end if*/
				else { /*current is the right kid*/
				    current->parent->right_kid = current->right_kid->right_kid;
				} /*end else*/
				
				if (current->right_kid->right_kid != NULL) {
				    current->right_kid->right_kid->parent = current->parent;

				    /*Check for new temp_kid*/
				    if ((current->right_kid->right_kid->me[0] == 'X')
					|| (current->right_kid->right_kid->me[0] == 'U')
					|| (current->right_kid->right_kid->me[0] == 'R')
					|| (current->right_kid->right_kid->me[0] == 'F')
					|| (current->right_kid->right_kid->me[0] == 'G')) {
					current->parent->temp_kid = 1;
				    } /*end if*/
				    /*else, temporal setting from other kid of parent reigns*/

				} /*end if*/
			    } /*end else*/
			    
			    /*delete the first negation*/
			    temp = current;
			    current = current->right_kid;
			    free (temp->me);
			    free (temp);
			    
			    /*delete the second negation*/
			    free (current->me);
			    free (current);
			    
			    /*Adjust the formula length*/
			    formula_length -= 4; /*2 per ~ operator*/
			    
			    break;
		    } /*end switch*/
		    break;
	    } /*end switch*/
	} /*end if*/
	
	if ((current->left_kid != NULL)
	    && (visited_left == 0)) {
		current = current->left_kid;
		/*sprintf(formula, "%s(", formula);*/
		continue;
	} /*end if*/
	
	else if ((current->right_kid != NULL)
		 && (visited_right == 0)) {
	    current = current->right_kid;
	    visited_left = 0;
	    visited_right = 0;
	    continue;
	} /*end else if*/
	else {
	    if (current->parent == NULL) {
		if (current != root) {
		    fprintf(stderr, "ERROR1: malformed parse tree detected in preorder traversal\n");
		    exit(1);
		} /*end if*/
		else { /*formula of length 1*/
		    visited_right = 1;
		    continue;
		} /*end else*/
	    } /*end if*/
	    
	    
	    if (current->parent->right_kid == current) {
		visited_right = 1;
	    } /*end if*/
	    else {
		visited_right = 0;
	    } /*end else*/
	    current = current->parent;
	    visited_left = 1;
	} /*end else*/
    } /*end while*/		
    
    return;
} /*end NoRForm*/


/* Function reduceOperators
   Purposes: (preorder traversal)
      (1) eliminates operator '->' from the formula (commented out)
      (2) eliminates double negations
      (3) applies rewriting reduction rules for tokens TRUE and FALSE ONLY

  Rewriting reduction rules (necessary to reduce the number of characters in
  a formula):
    (~ TRUE) => (FALSE)
    (~ FALSE) => (TRUE)
    (TRUE U a) => (F a)
    (FALSE R a) => (G a)
    (FALSE U a) => (a)
    (TRUE R a) => (a)
*/
void reduceOperators() {
  struct node *current = root;
  struct node *temp;
  short visited_left=0, visited_right=0;
  
  /*Error Check*/
  if((formula_length == 0) || (current == NULL)) {
    fprintf(stderr, "Warning: Can't reduce an empty formula\n");
    return;
  } /*end if*/
  
  if (verbose) {
    fprintf(stderr, "---------------------------\nREDUCING OPERATORS\n");
    fprintf(stderr, "formula before: \n");
    printFormula(formula_length);
    fprintf(stderr, "\n");
  } /*end if*/
  
  /*Loop while we haven't reached the root 
    after exploring it's right branch*/
  while (! ((current == root) && (visited_right == 1)) ) {
    
    if ((visited_left == 0)
	&& (visited_right == 0)) {
      
      /*Visit this node*/
      
      /*Check this node of the formula*/
      if (verbose) {
	fprintf(stderr, "3currently examining: %s", current->me);
	if (current->left_kid != NULL) {
	  fprintf(stderr, "; left kid=%s", current->left_kid->me);
	} /*end if*/
	if (current->right_kid!= NULL) {
	  fprintf(stderr, "; right kid=%s", current->right_kid->me);
	} /*end if*/
	fprintf(stderr, "\n");
      } /*end if*/
      switch (current->me[0]) {
      case '-' :
      case '>' : /*(a -> b) becomes ((~a) | b)*/
	if (verbose) {fprintf(stderr, "(a -> b) becomes ((~a) | b)\n"); }
	current->me[0] = '|';
	current->me[1] = '\0';
	negate(current->left_kid);
	
	/*Adjust the formula length*/
	formula_length++;
	
	break;
	
      case '~' : 
	/*(~~a) becomes a*/
	if ((current->right_kid != NULL)
	    && (current->right_kid->me[0] == '~')) {
	  /*We have a double negation*/
	  if (verbose) {fprintf(stderr, "(~~a) becomes (a)\n"); }

	  if (current->parent == NULL) {
	    /*We're at the root*/
	    
	    /*error checking*/
	    if (root != current) {
	      fprintf(stderr, "ERROR: non-root node with NULL parent!\n");
	      exit(1);
	    } /*end if*/
	    
	    /*reset the root*/
	    root = current->right_kid->right_kid;
	    if (root == NULL) {
	      fprintf(stderr, "ERROR: Negation with no right child!\n");
	      exit(1);
	    } /*end if*/
	    root->parent = NULL;
	  } /*end if*/
	  else { /*We're not at the root*/
	    if (current->parent->left_kid == current) {
	      current->parent->left_kid = current->right_kid->right_kid;
	    } /*end if*/
	    else { /*current is the right kid*/
	      current->parent->right_kid = current->right_kid->right_kid;
	    } /*end else*/
	    
	    if (current->right_kid->right_kid != NULL) {
	      current->right_kid->right_kid->parent = current->parent;
	    } /*end if*/
	  } /*end else*/
	  
	  /*delete the first negation*/
	  temp = current;
	  current = current->right_kid;
	  free (temp->me);
	  free (temp);
	  
	  /*delete the second negation*/
	  free (current->me);
	  free (current);
	  
	  /*Adjust the formula length*/
	  formula_length -= 4; /*2 per ~ operator*/
	  
	  break;
	} /*end if*/
	
	/*(~FALSE) becomes TRUE*/
	if ((current->right_kid != NULL)
	    && (strcmp(current->right_kid->me, "FALSE") == 0)) {
	  /*We have a ~FALSE*/
	  if (verbose) {
	    fprintf(stderr, "~FALSE -> TRUE\n");
	  } /*end if*/
	  
	  if (current->parent == NULL) {
	    /*We're at the root*/
	    
	    /*error checking*/
	    if (root != current) {
	      fprintf(stderr, "ERROR: non-root node with NULL parent!\n");
	      exit(1);
	    } /*end if*/
	    
	    /*reset the root*/
	    root = current->right_kid;
	    if (root == NULL) {
	      fprintf(stderr, "ERROR: Negation with no right child!\n");
	      exit(1);
	    } /*end if*/
	    root->parent = NULL;
	  } /*end if*/
	  else { /*We're not at the root*/
	    if (current->parent->left_kid == current) {
	      current->parent->left_kid = current->right_kid;
	    } /*end if*/
	    else { /*current is the right kid*/
	      current->parent->right_kid = current->right_kid;
	    } /*end else*/
	    
	    if (current->right_kid != NULL) {
	      current->right_kid->parent = current->parent;
	    } /*end if*/
	  } /*end else*/
	  
	  /*change the boolean*/
	  strcpy(current->right_kid->me, "TRUE");
	  
	  /*delete the negation*/
	  temp = current;
	  current = current->right_kid;
	  free (temp->me);
	  free (temp);
	  
	  /*Adjust the formula length*/
	  formula_length -= 2; /*2 per ~ operator*/
	  break;
	} /*end if*/
	
	/*(~TRUE) becomes FALSE*/
	if ((current->right_kid != NULL)
	    && (strcmp(current->right_kid->me, "TRUE") == 0)) {
	  /*We have a ~FALSE*/
	  if (verbose) {
	    fprintf(stderr, "~TRUE -> FALSE\n");
	  } /*end if*/
	  
	  if (current->parent == NULL) {
	    /*We're at the root*/
	    
	    /*error checking*/
	    if (root != current) {
	      fprintf(stderr, "ERROR: non-root node with NULL parent!\n");
	      exit(1);
	    } /*end if*/
	    
	    /*reset the root*/
	    root = current->right_kid;
	    if (root == NULL) {
	      fprintf(stderr, "ERROR: Negation with no right child!\n");
	      exit(1);
	    } /*end if*/
	    root->parent = NULL;
	  } /*end if*/
	  else { /*We're not at the root*/
	    if (current->parent->left_kid == current) {
	      current->parent->left_kid = current->right_kid;
	    } /*end if*/
	    else { /*current is the right kid*/
	      current->parent->right_kid = current->right_kid;
	    } /*end else*/
	    
	    if (current->right_kid != NULL) {
	      current->right_kid->parent = current->parent;
	    } /*end if*/
	  } /*end else*/
	  
	  /*change the boolean*/
	  strcpy(current->right_kid->me, "FALSE");
	  
	  /*delete the negation*/
	  temp = current;
	  current = current->right_kid;
	  free (temp->me);
	  free (temp);
	  
	  /*Adjust the formula length*/
	  formula_length -= 2; /*2 per ~ operator*/
	  break;
	} /*end if*/
	
	break;
	
      case 'U' :
	
	/*(TRUE U a) becomes (F a)*/
	if ((current->left_kid != NULL)
	    && (strcmp(current->left_kid->me, "TRUE") == 0)) {
	  /*We have a (FALSE U a)*/
	  if (verbose) {
	    fprintf(stderr, "(TRUE U a) => (F a)\n");
	  } /*end if*/
	  
	  /*delete the TRUE left kid*/
	  temp = current->left_kid;
	  free (temp->me);
	  free (temp);
	  current->left_kid = NULL;

	  /*change the operator*/
	  current->me[0] = 'F';

	  /*Adjust the formula length*/
	  formula_length -= 4; /*deleting TRUE*/
	  break;
	} /*end if*/

	/*(FALSE U a) becomes (a)*/
	if ((current->left_kid != NULL)
	    && (strcmp(current->left_kid->me, "FALSE") == 0)) {
	  /*We have a (FALSE U a)*/
	  if (verbose) {
	    fprintf(stderr, "(FALSE U a) => (a)\n");
	  } /*end if*/
	  
	  if (current->parent == NULL) {
	    /*We're at the root*/
	    
	    /*error checking*/
	    if (root != current) {
	      fprintf(stderr, "ERROR: non-root node with NULL parent!\n");
	      exit(1);
	    } /*end if*/
	    
	    /*reset the root*/
	    root = current->right_kid;
	    if (root == NULL) {
	      fprintf(stderr, "ERROR: U-operator with no right child!\n");
	      exit(1);
	    } /*end if*/
	    root->parent = NULL;
	  } /*end if*/
	  else { /*We're not at the root*/
	    if (current->parent->left_kid == current) {
	      current->parent->left_kid = current->right_kid;
	    } /*end if*/
	    else { /*current is the right kid*/
	      current->parent->right_kid = current->right_kid;
	    } /*end else*/
	    
	    if (current->right_kid != NULL) {
	      current->right_kid->parent = current->parent;
	    } /*end if*/
	  } /*end else*/
	  
	  /*delete the FALSE left kid*/
	  temp = current->left_kid;
	  free (temp->me);
	  free (temp);

	  /*delete the U*/
	  temp = current;
	  current = current->right_kid;
	  free (temp->me);
	  free (temp);
	  
	  /*Adjust the formula length*/
	  formula_length -= 6; /*deleting FALSE and U*/
	  break;
	} /*end if*/

	break;
	
      case 'R' :

	/*(FALSE R a) becomes (G a)*/
	if ((current->left_kid != NULL)
	    && (strcmp(current->left_kid->me, "FALSE") == 0)) {
	  /*We have a (FALSE U a)*/
	  if (verbose) {
	    fprintf(stderr, "(FALSE R a) => (G a)\n");
	  } /*end if*/
	  
	  /*delete the FALSE left kid*/
	  temp = current->left_kid;
	  free (temp->me);
	  free (temp);
	  current->left_kid = NULL;

	  /*change the operator*/
	  current->me[0] = 'G';

	  /*Adjust the formula length*/
	  formula_length -= 5; /*deleting FALSE*/
	  break;
	} /*end if*/

	/*(TRUE R a) becomes (a)*/
	if ((current->left_kid != NULL)
	    && (strcmp(current->left_kid->me, "TRUE") == 0)) {
	  /*We have a (TRUE R a)*/
	  if (verbose) {
	    fprintf(stderr, "(TRUE R a) => (a)\n");
	  } /*end if*/
	  
	  if (current->parent == NULL) {
	    /*We're at the root*/
	    
	    /*error checking*/
	    if (root != current) {
	      fprintf(stderr, "ERROR: non-root node with NULL parent!\n");
	      exit(1);
	    } /*end if*/
	    
	    /*reset the root*/
	    root = current->right_kid;
	    if (root == NULL) {
	      fprintf(stderr, "ERROR: R-operator with no right child!\n");
	      exit(1);
	    } /*end if*/
	    root->parent = NULL;
	  } /*end if*/
	  else { /*We're not at the root*/
	    if (current->parent->left_kid == current) {
	      current->parent->left_kid = current->right_kid;
	    } /*end if*/
	    else { /*current is the right kid*/
	      current->parent->right_kid = current->right_kid;
	    } /*end else*/
	    
	    if (current->right_kid != NULL) {
	      current->right_kid->parent = current->parent;
	    } /*end if*/
	  } /*end else*/
	  
	  /*delete the TRUE left kid*/
	  temp = current->left_kid;
	  free (temp->me);
	  free (temp);

	  /*delete the R*/
	  temp = current;
	  current = current->right_kid;
	  free (temp->me);
	  free (temp);
	  
	  /*Adjust the formula length*/
	  formula_length -= 5; /*deleting TRUE and R*/
	  break;
	} /*end if*/

	break;

      default :
	/*This doesn't work if there's any default statement here*/
	break;
      } /*end switch*/
      
      /*Done visiting this node*/

    } /*end if*/

    if ((current->left_kid != NULL)
	&& (visited_left == 0)) {
      if (verbose) {fprintf(stderr, "moving from current(%s) to left kid(%s)\n", current->me, current->left_kid->me);}
      current = current->left_kid;
      continue;
    } /*end if*/

    else if ((current->right_kid != NULL)
	     && (visited_right == 0)) {
      if (verbose) {fprintf(stderr, "moving from current(%s) to right kid(%s)\n", current->me, current->right_kid->me);}
      current = current->right_kid;
      visited_left = 0;
      visited_right = 0;
      continue;
    } /*end else if*/
    else {
      if (current->parent == NULL) {
	if (current != root) {
	  fprintf(stderr, "ERROR4: malformed parse tree detected in preorder traversal\n");
	  exit(1);
	} /*end if*/
	else { /*formula of length 1*/
	  visited_right = 1;
	  continue;
	} /*end else*/
      } /*end if*/
	    
      if (current->parent->right_kid == current) {
	visited_right = 1;
      } /*end if*/
      else {
	visited_right = 0;
      } /*end else*/
      current = current->parent;
      visited_left = 1;
    } /*end else*/
  } /*end while*/	
  
  return;
} /*end reduceOperators*/


/* Function negNormalForm

In one pre-order traversal, transforms the formula into NNF and reduces the operators.
    Purposes:
      (1) eliminates operator '->' from the formula
      (2) eliminates double negations
      (3) moves ~'s inside to propositions
      (4) for TGBA: combines GF into one operator
*/
void negNormalForm() {
    struct node *current = root;
    struct node *temp;
    short visited_left=0, visited_right=0;

    /*Error Check*/
    if((formula_length == 0) || (current == NULL)) {
	fprintf(stderr, "Warning: Can't print an empty formula\n");
	return;
    } /*end if*/

    if (verbose) {
	fprintf(stderr, "---------------------------\nNegNormalForm: root is %s\n", root->me);
    } /*end if*/
        
    /*Loop while we haven't reached the root 
      after exploring it's right branch*/
    while (! ((current == root) && (visited_right == 1)) ) {
	if ((visited_left == 0)
	    && (visited_right == 0)) {
	    
            /*Visit this node*/
	    
	    /*Check this node of the formula*/
	    if (verbose) {
		fprintf(stderr, "4currently examining: %s\n", current->me);
	    } /*end if*/
	    switch (current->me[0]) {
		case '-' :
		case '>' : /*(a -> b) becomes ((~a) | b)*/
		    current->me[0] = '|';
		    current->me[1] = '\0';
		    
		    /*This node could have temp_kid set because of left_kid; check*/
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

		    negate(current->left_kid);
		    		    
		    break;
		    
		case '~' : 
		    if (current->right_kid == NULL) {
			fprintf(stderr, "ERROR: Negation with no right child!\n");
			exit(1);
		    } /*end if*/
		    
		    switch (current->right_kid->me[0]) {
			
			case '~' : /*(~~a) becomes a*/
			    /*We have a double negation*/
			    
			    if (current->parent == NULL) {
				/*We're at the root*/
				
				/*error checking*/
				if (root != current) {
				    fprintf(stderr, "ERROR: non-root node with NULL parent!\n");
				    exit(1);
				} /*end if*/
				
				/*reset the root*/
				root = current->right_kid->right_kid;
				if (root == NULL) {
				    fprintf(stderr, "ERROR: Negation with no right child!\n");
				    exit(1);
				} /*end if*/
				root->parent = NULL;
			    } /*end if*/
			    else { /*We're not at the root*/
				if (current->parent->left_kid == current) {
				    current->parent->left_kid = current->right_kid->right_kid;
				} /*end if*/
				else { /*current is the right kid*/
				    current->parent->right_kid = current->right_kid->right_kid;
				} /*end else*/
				
				if (current->right_kid->right_kid != NULL) {
				    current->right_kid->right_kid->parent = current->parent;
				    
				    /*Check for new temp_kid*/
				    if ((current->right_kid->right_kid->me[0] == 'X')
					|| (current->right_kid->right_kid->me[0] == 'U')
					|| (current->right_kid->right_kid->me[0] == 'R')
					|| (current->right_kid->right_kid->me[0] == 'F')
					|| (current->right_kid->right_kid->me[0] == 'G')) {
					current->parent->temp_kid = 1;
				    } /*end if*/
				    /*else, temporal setting from other kid of parent reigns*/

				} /*end if*/
			    } /*end else*/
			    
			    /*delete the first negation*/
			    temp = current;
			    current = current->right_kid;
			    free (temp->me);
			    free (temp);
			    
			    /*delete the second negation*/
			    free (current->me);
			    free (current);
			    
			    /*Adjust the formula length*/
			    formula_length -= 4; /*2 per ~ operator*/
			    
			    break;
			    
			case '&' : /*~(a & b) becomes ((~a) | (~b))*/
			    temp = current->right_kid;
			    current->left_kid = temp->left_kid;
			    current->right_kid = temp->right_kid;
			    current->left_kid->parent = current;
			    current->right_kid->parent = current;
			    
			    /*Remove the now-disconnected node*/
			    free (temp->me);
			    free (temp);
			    
			    /*Adjust the formula length*/
			    formula_length -= 2; /*eliminate one ~ operator*/
			    
			    current->me[0] = '|';
			    negate(current->left_kid);
			    negate(current->right_kid);
			    
			    break;
			    
			case '|' : /*(~(a | b)) becomes ((~a) & (~b))*/
			    temp = current->right_kid;
			    current->left_kid = temp->left_kid;
			    current->right_kid = temp->right_kid;
			    current->left_kid->parent = current;
			    current->right_kid->parent = current;
			    
			    /*Remove the now-disconnected node*/
			    free (temp->me);
			    free (temp);
			    
			    /*Adjust the formula length*/
			    formula_length -= 2; /*eliminate one ~ operator*/
			    
			    current->me[0] = '&';
			    negate(current->left_kid);
			    negate(current->right_kid);
			    break;
			    
			case 'X' : /*~(X a) becomes X(~a)*/
			  
			  if (strcmp(current->right_kid->me, "X") != 0) { 
			    /*don't change props starting with this letter*/
			    break;
			  } /*end if*/
			  
			    current->me[0] = 'X';
			    current->temp_kid = 0; /*reset to 0 since X isn't kid anymore*/
			    
			    if (current->parent != NULL) {
				/*We're not at the root*/
				
				current->parent->temp_kid = 1; /*our parent now has a temp kid*/
			    } /*end if*/

			    current->right_kid->me[0] = '~';
			    
			    break;

			case 'U' : /*~(a U b) becomes ((~a) R (~b))*/
			  
			  if (strcmp(current->right_kid->me, "U") != 0) { 
			    /*don't change props starting with this letter*/
			    break;
			  } /*end if*/

			    temp = current->right_kid;
			    current->left_kid = temp->left_kid;
			    current->right_kid = temp->right_kid;
			    current->left_kid->parent = current;
			    current->right_kid->parent = current;
			    
			    /*Remove the now-disconnected node*/
			    free (temp->me);
			    free (temp);
			    
			    /*Adjust the formula length*/
			    formula_length -= 2; /*eliminate one ~ operator*/
			    
			    current->me[0] = 'R';

			    if (current->parent != NULL) {current->parent->temp_kid = 1;}
			    current->temp_kid = 0; /*now ~ will be both kids*/

			    negate(current->left_kid);
			    negate(current->right_kid);

			    break;
			    
			case 'R' : /*~(a R b) becomes ((~a) U (~b))*/

			  if (strcmp(current->right_kid->me, "R") != 0) { 
			    if (verbose) {
			      fprintf(stderr, "Found %s ... R-var... skipping\n", current->right_kid->me);
			    } /*end if*/
			    /*don't change props starting with this letter*/
			    break;
			  } /*end if*/
			  else {
			    if (verbose) {
			      fprintf(stderr, "Found %s ... R-operator... processing\n", current->right_kid->me);
			    } /*end if*/
			  } /*end else*/

			    temp = current->right_kid;
			    current->left_kid = temp->left_kid;
			    current->right_kid = temp->right_kid;
			    current->left_kid->parent = current;
			    current->right_kid->parent = current;
			    
			    /*Remove the now-disconnected node*/
			    free (temp->me);
			    free (temp);
			    
			    /*Adjust the formula length*/
			    formula_length -= 2; /*eliminate one ~ operator*/
			    
			    current->me[0] = 'U';

			    if (current->parent != NULL) {current->parent->temp_kid = 1;}
			    current->temp_kid = 0; /*now ~ will be both kids*/

			    negate(current->left_kid);
			    negate(current->right_kid);
			    
			    break;
			    
			case 'G' : /*~(G a) becomes F(~a)*/
			  
			  if (strcmp(current->right_kid->me, "G") != 0) { 
			    /*don't change props starting with this letter*/
			    break;
			  } /*end if*/

			    current->me[0] = 'F';
			    if (current->parent != NULL) {current->parent->temp_kid = 1;}
			    current->right_kid->me[0] = '~';
			    current->temp_kid = 0; /*now ~ will be the kid*/

			    break;
			    
			case 'F' :/*~(F a) becomes G(~a)*/
			  
			  if (strcmp(current->right_kid->me, "F") != 0) { 
			    /*don't change props starting with this letter*/
			    break;
			  } /*end if*/

			    current->me[0] = 'G';
			    if (current->parent != NULL) {current->parent->temp_kid = 1;}
			    current->right_kid->me[0] = '~';
			    current->temp_kid = 0; /*now ~ will be the kid*/

			    break;
			    
			default : 
			    /*This doesn't work if there's any default statement here*/
			    /* -- it dies on propositions then*/
			    break;
		    } /*end switch*/
		    
		default : 
		    /*This doesn't work if there's any default statement here*/
		    break;
	    } /*end switch*/

	    /*another switch in case current is now F*/
	    switch (current->me[0]) {
		
		case 'F' : /*look for GF and combine into one operator for TGBA*/
		  
		  if (strcmp(current->me, "F") != 0) { 
		    /*don't change props starting with this letter*/
		    break;
		  } /*end if*/

		    if ((tgba) 
			&& (current->parent != NULL)
			&& (strcmp(current->parent->me, "G") == 0)) {
			
			strcpy(current->parent->me, "GF");
			//fprintf(stderr, "Found a GF!\n");

			temp = current;
			current = current->parent;
			
			current->right_kid = current->right_kid->right_kid;
			current->right_kid->parent = current;
			
			
			/*delete the extra node*/
			free (temp->me);
			free (temp);
			
			/*Reset temp_kid*/
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
			
		    } /*end if*/
		    break;
		    
	    } /*end switch*/
	    
	} /*end if*/
	
	if ((current->left_kid != NULL)
	    && (visited_left == 0)) {
		current = current->left_kid;
		/*sprintf(formula, "%s(", formula);*/
		continue;
	} /*end if*/

	else if ((current->right_kid != NULL)
		 && (visited_right == 0)) {
	    current = current->right_kid;
	    visited_left = 0;
	    visited_right = 0;
	    continue;
	} /*end else if*/
	else {
	    if (current->parent == NULL) {
		if (current != root) {
		    fprintf(stderr, "ERROR2: malformed parse tree detected in preorder traversal\n");
		    exit(1);
		} /*end if*/
		else { /*formula of length 1*/
		    visited_right = 1;
		    continue;
		} /*end else*/
	    } /*end if*/
	    
	    if (current->parent->right_kid == current) {
		visited_right = 1;
	    } /*end if*/
	    else {
		visited_right = 0;
	    } /*end else*/
	    current = current->parent;
	    visited_left = 1;
	} /*end else*/
    } /*end while*/	
    
    return;
} /*end negNormalForm*/



/* Function build_el_list_preorder
   Purposes:
      (1) builds the el_list of elementary formulas using 'X,' 'U,' 'R,' 'G', and 'F'
      (2) for variable ordering: calls printSubformulaVar_makeGraph instead of 
          printSubformulaVar to make the variable-subformula-graph
      (3) for substitution: fills in the temp_kid boolean at each node to designate
          whether the node has any temporal operators among its descendants.

WARNING: TEMP_KID ALREADY SET BY yaccLTL.cc and negate()

*/
void build_el_list_preorder() {
    struct node *current = root;
    int i = 0;
    short visited_left=0, visited_right=0;
    int level_counter = 0;    /*start at level 0: the root*/
    int last = -1;            /*the id number of the last variable above this one*/
    /*int last_level = -1;      /*the level of the parse tree 'last' is located at*/
    struct node *runner;      /*a pointer to run to up the root looking for vars*/
    int runner_level;         /*the level the runner is currently at*/

    KItem search;            /*a variable name to search for*/

    /*Error Check*/
    if(current == NULL) {
	fprintf(stderr, "Warning: Can't reduce an empty formula\n");
	return;
    } /*end if*/
 
    if (verbose) {
	fprintf(stderr, "---------------------------\nBUILDING el_list\n");
    } /*end if*/
    
  
    /*Since we'll always have at least one EL_var (EL_f) for TGBA encodings,
      go ahead and write the heading here*/
    if (tgba) {
	if (smvFlag == 'c') { /*CadenceSMV-style comments*/
	    //fprintf(OUT, "VAR \n   /*and declare a new variable for each EL_var in el_list*/\n");
	    fprintf(OUT, "VAR \n   /*and declare a new variable for each EL_var in el_list*/\n");
	} /*end if*/
	else if ((smvFlag == 'n') || (smvFlag == 'j')) { /*NuSMV-style comments*/
	    //fprintf(OUT, "VAR \n   -- and declare a new variable for each EL_var in el_list\n");
	    fprintf(OUT, "VAR \n   -- and declare a new variable for each EL_var in el_list\n");
	} /*end else if*/
	else { /*SAL-style comments*/
	    fprintf(OUT, "\n     OUTPUT\n");
	    //fprintf(OUT, "     %%and declare a new variable for each EL_var in el_list\n");
	    fprintf(OUT, "     %%and declare a new variable for each EL_var in el_list\n");
	} /*end else*/
    } /*end if*/


    /*Loop while we haven't reached the root 
      after exploring it's right branch*/
    while (! ((current == root) && (visited_right == 1)) ) {

	if (verbose == 1) {
	    fprintf(stderr, "Variables:\n");
	    for (i = 0; i < varList.size(); i++) {
		fprintf(stderr, "   %d: (%s)\n", i, varList.findName(i).c_str());
	    } /*end for*/
	} /*end if*/

	if ((visited_left == 0)
	    && (visited_right == 0)) {
	    
	    /*Check this node of the formula*/
	    if (verbose) {
		fprintf(stderr, "6currently examining: %s (#%d)\n", current->me, current->num);
	    } /*end if*/
	    switch (current->me[0]) {
		case '~' :
		case '&' :
		case '|' :
		case '-' : /*implies*/
		case '>' : /*implies*/
		    current->num = printSubformulaVar_makeGraph(current);
		    if ((verbose) && (current->num != -1)) {
			fprintf(stderr, "Just found non-temporal var %s (var #%d)\n", current->me, current->num);
		    } /*end if*/
		    break;
		case 'X' : 
		  
		  if (strcmp(current->me, "X") != 0) { 
		    /*don't change props starting with this letter*/
		    break;
		  } /*end if*/

		    if ((tgba == 0) && (nextOpPresent == 0)) {
			if (smvFlag == 'c') { /*CadenceSMV-style comments*/
			    //fprintf(OUT, "VAR \n   /*and declare a new variable EL_X_g for each formula (X g) in el_list*/\n");
			    fprintf(OUT, "VAR \n   /*and declare a new variable EL_X_g for each formula (X g) in el_list\n     generated by a primary operator X, U, R, G, or F*/\n");
			} /*end if*/
			else if ((smvFlag == 'n') || (smvFlag = 'j')) { /*NuSMV-style comments*/
			    //fprintf(OUT, "VAR \n   -- and declare a new variable EL_X_g for each formula (X g) in el_list\n");
			    fprintf(OUT, "VAR \n   -- and declare a new variable EL_X_g for each formula (X g) in el_list\n   -- generated by a primary operator X, U, R, G, or F\n");
			} /*end else if*/
			else { /*SAL-style comments*/
			    fprintf(OUT, "\n     OUTPUT\n");
			    //fprintf(OUT, "     %%and declare a new variable EL_X_g for each formula (X g) in el_list\n");
			    fprintf(OUT, "     %%and declare a new variable EL_X_g for each formula (X g) in el_list\n     %%generated by a primary operator X, U, R, G, or F\n");
			} /*end else*/
		    } /*end if*/
		    if (smvFlag == 's') { fprintf(OUT, "       "); } /*indent SAL module*/
		    /*fprintf(OUT, "EL"); OLD*/
		    nextOpPresent = 1;

		    /*check that this node is properly labeled before calling printSubformulaVar_makegraph*/
		    if (current->right_kid != NULL) { 
			if ( (current->right_kid->me[0] == 'X')
			     || (current->right_kid->me[0] == 'U')
			     || (current->right_kid->me[0] == 'R')
			     || (current->right_kid->me[0] == 'G')
			     || (current->right_kid->me[0] == 'F') ) {
			    current->temp_kid = 1;
			} /*end if*/
		    } /*end if*/
		    else {
			fprintf(stderr, "ERROR: X-operator with no right kid\n");
			exit(0);
		    } /*end else*/

                    /*store the id number of this subformula at this node*/
		    current->num = printSubformulaVar_makeGraph(current);
		    
		    if (tgba) { /*if there is guaranteed to be a var kid*/

		    } /*end if*/

		    break;
		case 'U' : 
		case 'R' :
		case 'G' :
		case 'F' :
		  
		  if ((strlen(current->me) > 1) && (strcmp(current->me, "GF") != 0)) { 
		    /*don't change props starting with this letter*/
		    break;
		  } /*end if*/

		    /* case 'GF' is also included in this for tgba */
		    if (! ( (current->parent != NULL) 
			    && (current->parent->me[0] == 'X') ) ) {
			if ((tgba == 0) && (nextOpPresent == 0)) {
			    if (smvFlag == 'c') { /*CadenceSMV-style comments*/
				//fprintf(OUT, "VAR \n   /*and declare a new variable EL_X_g for each formula (X g) in el_list*/\n");
				fprintf(OUT, "VAR \n   /*and declare a new variable EL_X_g for each formula (X g) in el_list\n     generated by a primary operator X, U, R, G, or F*/\n");
			    } /*end if*/
			    else if ((smvFlag == 'n') || (smvFlag = 'j')) { /*NuSMV-style comments*/
				//fprintf(OUT, "VAR \n   -- and declare a new variable EL_X_g for each formula (X g) in el_list\n");
				fprintf(OUT, "VAR \n   -- and declare a new variable EL_X_g for each formula (X g) in el_list\n   -- generated by a primary operator X, U, R, G, or F\n");
			    } /*end else if*/
			    else { /*SAL-style comments*/
				fprintf(OUT, "     OUTPUT\n");
				//fprintf(OUT, "     %%and declare a new variable EL_X_g for each formula (X g) in el_list\n");
				fprintf(OUT, "     %%and declare a new variable EL_X_g for each formula (X g) in el_list\n     %%generated by a primary operator X, U, R, G, or F\n");
			    } /*end else*/
			} /*end if*/
			if (smvFlag == 's') { fprintf(OUT, "       "); } /*indent SAL module*/
			/*fprintf(OUT, "EL_X"); OLD*/
			nextOpPresent = 1;
		    } /*end if*/

		    /*store the id number of this subformula at this node*/
		    current->num = printSubformulaVar_makeGraph(current);
		    if ((current->num == -1) && (tgba)) {
			/*there are vars for the next-time of these, not these exactly, for gba encoding*/
			fprintf(stderr, "ERROR: -1 returned from printSubformulaVar_makeGraph for %s-subformula\n", current->me);
		    } /*end if*/
		    break;
		default : /*This is a leaf: a propositional variable*/
		    if (verbose == 1) {
			fprintf(stderr, "Reached leaf: %s (#%d)\n", current->me, current->num);
		    } /*end if*/
		    
		    search.setName(current->me);
		    if ( ! (varList.query(search))) { /*if we haven't encountered this leaf before*/
			current->num = varList.addItem(search); /*record the variable number*/
			if (verbose == 1) {
			    fprintf(stderr, "adding item %s to varlist1\n", search.getName().c_str());
			} /*end if*/
			if (varOrder != 'z') {
			    /*Make self-loops at all vertices in the graph*/
			    //fprintf(stderr, "connect18\n");
			    connect_graph(current->num, current->num);
			} /*end if*/
		    } /*end if*/
		    else { /*variable already recorded*/
			if (current->num == -1) { 
			    current->num = (varList.find(search)).getInfo();
			    if (verbose) {
				fprintf(stderr, "labeling var %s with number %d\n", current->me, current->num);
			    } /*end if*/
			} /*end if*/
			else if (verbose) {
			    fprintf(stderr, "current->num is %d\n", current->num);
			} /*end if*/
		    } /*end else*/

		    if (varOrder != 'z') {
			if (current->num == -1) { 
			    fprintf(stderr, "ERROR5: leaf %s has id number -1\n", current->me);
			    exit(1);
			} /*end if*/
			else {
			    if (verbose) {
				fprintf(stderr, "Leaf! Number %d\n", current->num); 
			    } /*end if*/
			} /*end else*/
		    } /*end if*/
		    break;
	    } /*end switch*/

	    if ((varOrder != 'z') && (current->num != -1)) {  /*if we're at a variable node*/
		/*try to connect this node to something: send the runner up*/    
		
		last = -1; /*reset*/
		runner = current;
		while (runner->parent != NULL) {
		    runner = runner->parent; /*go up a level*/
		    
		    /*check for a last var*/
		    if (runner->num != -1) {
			last = runner->num;
			if (verbose == 1) {
			    fprintf(stderr, "1 last var is now %d\n", last);
			} /*end if*/
			break;
		    } /*end if*/
		    else if (runner == root) {
			if (tgba) {
			    fprintf(stderr, "Shouldn't get here in TGBA... The root should be a var.\n");
			} /*end if*/
			break;
		    } /*end if*/
		} /*end while*/
		
		if ((last != -1) && (current->num != -1)) {
		    //fprintf(stderr, "connect19\n");
		    connect_graph(current->num, last);
		} /*end if*/
		
	    } /*end if*/
	    
	    if (verbose) {
		fprintf(stderr, "3done examining: %s (#%d)\n", current->me, current->num);
	    } /*end if*/

	} /*end if*/
	
	if ((current->left_kid != NULL)
	    && (visited_left == 0)) {
		current = current->left_kid;
		level_counter++; /*going down: increase the tree level*/
		if (verbose == 1) {
		    fprintf(stderr, "Going down left; level is now %d\n", level_counter);
		} /*end if*/
		continue;
	} /*end if*/
	else if ((current->right_kid != NULL)
		 && (visited_right == 0)) {

	    current = current->right_kid;
	    level_counter++; /*going down: increase the tree level*/
	    if (verbose == 1) {
		fprintf(stderr, "Going down right; level is now %d\n", level_counter);
	    } /*end if*/
	    visited_left = 0;
	    visited_right = 0;
	    continue;
	} /*end else if*/
	else {
	    if (current->parent == NULL) {
		if (current != root) {
		    fprintf(stderr, "ERROR3: malformed parse tree detected in preorder traversal\n");
		    exit(1);
		} /*end if*/
		else { /*formula of length 1*/
		    visited_right = 1;
		    continue;
		} /*end else*/
	    } /*end if*/
	    
	    if (current->parent->right_kid == current) {
		visited_right = 1;
	    } /*end if*/
	    else {
		visited_right = 0;
	    } /*end else*/
	    current = current->parent;
	    level_counter--;  /*going up: decrease the tree level*/
	    if (verbose == 1) {
		fprintf(stderr, "Going up; level is now %d\n", level_counter);
	    } /*end if*/
	    visited_left = 1;
	} /*end else*/

	i++;
	/*if (i == 6) {exit(0);}*/
    } /*end while*/	

    return;
} /*end build_el_list_preorder*/


void deleteTree() {
    struct node *current = root;
    struct node *doomed;
    int i = 0;
    short visited_left=0, visited_right=0;

    /*Error Check*/
    if(current == NULL) {
	fprintf(stderr, "Tree already deleted\n");
	return;
    } /*end if*/

    while (! ((current == root) && (visited_right == 1)) ) {

	if (visited_left == 1) {
	    visited_left = 0;
	} /*end if*/
	else {
	    if (current->left_kid != NULL) {
		current = current->left_kid;
		continue;
	    } /*end if*/
	} /*end else*/

	if (visited_right == 1) {
	    visited_right = 0;
	} /*end if*/
	else {
	    if (current->right_kid != NULL) {
		current = current->right_kid;
		continue;
	    } /*end if*/
	    else {
		if (current == root) {
		    visited_right = 1;
		    continue;
		} /*end if*/
	    } /*end else*/
	} /*end else*/

	/*Tie up the loose ends*/
	doomed = current;
	if (current->parent != NULL) {
	    visited_left = 1;
	    current->parent->left_kid = NULL;
	    if (current->parent->right_kid == current) {
		visited_right = 1;
		current->parent->right_kid = NULL;
	    } /*end if*/
	    current = current->parent;
	} /*end if*/

	/*Delete this node*/
	if (verbose) {
	    fprintf(stderr, "deleting node %s\n", doomed->me);
	} /*end if*/
	free(doomed->me);
	free(doomed);

	i++;

    } /*end while*/	

    if (verbose) {
	fprintf(stderr, "Deleting the root: %s\n", root->me);
    } /*end if*/
    free(root->me);
    free(root);

    return;
} /*end deleteTree*/


void printUsage() {
	fprintf(stderr, "Usage: PANDA (([(-c|-n|-s) (-nnf | -bnf) (-sloppy | -fussy) (-gba | -tgba) [(-mcs & (-max | -min | -random | -zero) | -lexm | -lexp | -linear [-reverse]) -v]] | (-pbnf | -pnnf | -pnor) LTL_formula_file\n");
	fprintf(stderr, "\twhere LTL_formula_file contains one line: a formula in the following syntax.\n");
	fprintf(stderr, "\tOperators (in order of precedence):\n");
	fprintf(stderr, "\t~ (not), & (and), | (or), -> (implication)\n");
	fprintf(stderr, "\tplus the following temoral operators:\n");
	fprintf(stderr, "\tX p is true at time t if p is true at time t + 1.\n");
	fprintf(stderr, "\tG p is true at time t if p is true at all times t' >= t.\n");
	fprintf(stderr, "\tF p is true at time t if p is true at some time t' >= t.\n");
	fprintf(stderr, "\tp U q is true at time t if q is true at some time t' >= t, and for all times < t' but >= t, p is true.\n");
	fprintf(stderr, "\tp R q is true at time t if either q is true at time t and all times following t, or if p is true at some time t' >= t, and for all times between t and t', inclusive, q is true.\n");
	fprintf(stderr, "\tOptional Flags:\n");
	fprintf(stderr, "\t  -pbnf to ONLY print formula in Boolean Normal Form and exit OR\n");
	fprintf(stderr, "\t  -pnnf to ONLY print formula in Negation Normal Form and exit OR\n");
	fprintf(stderr, "\t  -pnor to ONLY print formula without R-operators and exit OR\n");
	fprintf(stderr, "\t  -n for NuSMV-style comments in the symbolic automaton OR\n");
	fprintf(stderr, "\t  -c (default) for CadenceSMV-style comments in the symbolic automaton OR\n");
	fprintf(stderr, "\t  -s for SAL-style symbolic automaton AND\n");
	fprintf(stderr, "\t  -nnf to convert the formula to NNF in the parse tree OR\n");
	fprintf(stderr, "\t  -bnf (default) use Boolean Normal Form AND\n");
	fprintf(stderr, "\t  -fussy (default) use fussy encoding OR\n");
	fprintf(stderr, "\t  -sloppy for sloppy encoding (default is fussy encoding)\n");
	fprintf(stderr, "\t       (-sloppy option can only be used with NNF formulas!)\n");
	fprintf(stderr, "\t  -gba for CGH's standard state-based symbolic automaton (default)\n");
	fprintf(stderr, "\t  -tgba for transition-based symbolic automaton instead of default state-based one\n");
	fprintf(stderr, "\t  -mcs for MCS variable order\n");
	fprintf(stderr, "\t       -max to start with the maximum output degree node (default)\n");
	fprintf(stderr, "\t       -min to start with the minimum output degree node\n");
	fprintf(stderr, "\t       -random to start with a random node\n");
	fprintf(stderr, "\t       -zero to start with the first node encountered\n");
	fprintf(stderr, "\t  -lexm for LEXM variable order\n");
	fprintf(stderr, "\t  -lexp for LEXP variable order\n");
	fprintf(stderr, "\t  -linear for Linear variable order\n");
	fprintf(stderr, "\t  -reverse to reverse a flag-specified variable ordering\n");
	fprintf(stderr, "\t       (default is to use the Model Checker's default var order\n");
	fprintf(stderr, "\t  -v for verbose mode\n");
	exit(1);
} /*end printUsage()*/


/****************************************************************
Functions for Variable Ordering:
   mcs_order (which actually returns MCS order reversed)
   lexm_order
   lexp_order
   linear_order
   reverseOrderArray
- and support functions
*****************************************************************/


/**
 * Given the array with order of the variables, reverse the
 * order. Assumes that the array has length @automaton_size, which is
 * defined externally.
 */
void reverseOrderArray() {

    int automaton_size = varList.size();

    if (order_array == NULL) {
	return;
    } /*end if*/

    int* temp =  (int*) malloc (automaton_size * sizeof(int));

    for (int i=0; i<automaton_size; i++) {
	temp[i] = order_array[automaton_size - i - 1];
    } /*end if*/

    for (int i=0; i<automaton_size; i++) {
	order_array[i] = temp[i];
    } /*end for*/
    
    free(temp);
    return;
} /*end reverseOrderArray*/


/**
 * Returns the node in the graph that has the lowest out-degree. Ties
 * are broken somewhat arbitrarily (select the first such node). 
 */
int getMinDegreeNode() {
    int automaton_size = varList.size();
    int minOutDegree = 0;
    int selectedNode = 0;
    int currOutDegree = 0;
    KItem thisItem;

    for (int i = 0; i < automaton_size; i++) {
	
	thisItem = varList.findItemByNumber(i);
	currOutDegree = thisItem.getOutDegree();
	//fprintf(stderr, "The out degree of %s is %d\n", thisItem.getName().c_str(), currOutDegree);
	
	if (i == 0) { minOutDegree = currOutDegree; selectedNode = 0; continue; }

	if (currOutDegree < minOutDegree) {
	    minOutDegree = currOutDegree;
	    selectedNode = i;
	} /*end if*/
    } /*end for*/
    
    return selectedNode;
} /*end getMinDegreeNode*/


/**
 * Returns the node in the graph that has the highest out-degree. Ties
 * are broken somewhat arbitrarily (select the first such node). 
 */
int getMaxDegreeNode() {
    int automaton_size = varList.size();
    int maxOutDegree = 0;
    int selectedNode = 0;
    int currOutDegree = 0;
    KItem thisItem;

    for (int i = 0; i < automaton_size; i++) {
	
	thisItem = varList.findItemByNumber(i);
	currOutDegree = thisItem.getOutDegree();
	//fprintf(stderr, "The out degree of %s is %d\n", thisItem.getName().c_str(), currOutDegree);
	
	if (i == 0) { maxOutDegree = currOutDegree; selectedNode = 0; continue; }

	if (maxOutDegree < currOutDegree) {
	    maxOutDegree = currOutDegree;
	    selectedNode = i;
	} /*end if*/
    } /*end for*/
  
  return selectedNode;
} /*end getMaxDegreeNode*/


/** 
 * Reads the transition graph from A and B defined externally and
 * produces a variable order based on maximum cardinality
 * search. Using the algorithm defined in RGL.

 * @param automaton_size defined externally to be the size of the
 * automaton and thus the number of nodes in the graph.
 
 */
void mcs_order() {
    int automaton_size = varList.size();
    int initial_node;
    int i, j;

    if (verbose == 1) {
	fprintf (stderr, "MCS order here: ordering a graph with %d nodes...\n", automaton_size);
	fprintf (stderr, " %d nodes in varList...\n", varList.size());
    } /*end if*/

    /*determineMCSinitialNode here: */
    /*fprintf(stderr, "Determine the initial node for %s\n", mcs_start2str(mcs_start_at));*/
     
    if (mcs_start_node == MIN) {
	initial_node = getMinDegreeNode();
    } /*end if*/
    else if (mcs_start_node == MAX) {
	initial_node = getMaxDegreeNode();
    } /*end if*/
    else if (mcs_start_node == ZERO) {
        initial_node = 0;
    } /*end if*/
    else if (mcs_start_node == RANDOM) {
	initial_node = rand() % automaton_size;
    } /*end if*/
    else {
	fprintf(stderr, "Unknown mcs_start_node variable %d\n", 
		   mcs_start_node);
	return; /*this line should be unreachable*/
    } /*end else*/

    if (verbose == 1) {
	fprintf(stderr, "The initial node is %d\n", initial_node);
    } /*end if*/

    /*Error checking*/
    if (order_array == NULL) {
	fprintf(stderr, "ERROR: order_array is NULL! Exiting...\n");
	exit(1);
    } /*end if*/

    mcs_graph(var_graph, initial_node, order_array);
    //printf("DEBUG MODE: mcs_graph() returned back to me\n");
    
    /*The MCS order returned from rgl2 is actually the reversed order*/
    /*So, we fix it here*/
    reverseOrderArray();

    if (verbose == 1) {     /*DEBUG*/
	fprintf(stderr, "The mcs order is:\n");
	for (i = 0; i < automaton_size; i++) {
	    j = order_array[i];
	    fprintf(stderr, "   %d: %d (%s)\n", i, j, varList.findName(j).c_str());
	} /*end for*/
    } /*end if*/

    free_graph(var_graph);

    return;
} /*end mcs_order*/



/**
 * Orders the variables according to the LEXM heuristic as referenced
 * in Pan's SAT'04 paper. Uses the RGL package for the heuristic
 * implementation.
 */
void lexm_order() {
    lexicographic_bfs_graph_min(var_graph, 0, order_array);
    free_graph(var_graph);
    return;
} /*end lexm_order*/



/**
 * Orders the variables according to the LEXP heuristic as referenced
 * in Pan's SAT'04 paper. Uses the RGL package for the heuristic
 * implementation.
 */
void lexp_order() {
    lexicographic_bfs_graph(var_graph, 0, order_array);
    free_graph(var_graph);
    return;
} /*end lexp_order*/



/**
 * Orders the variables linearly. It is probably a horrible order
 * unless the model is highly linear itself.
 */
void linear_order() {
    int automaton_size = varList.size();

    for (int i=0; i<automaton_size; i++) {
	order_array[i] = i; /*warning: this will break if vars are ever removed from varList*/
    } /*end for*/
    
    return;
} /*end linear_order*/


/****************************************************************
Main Program
1) Read command-line arguments and set flags accordingly
2) Parse the formula via yyparse()
2.5) Reduce the formula via reduceOperators()
3) Convert the formula to a normal form via negNormalForm() or boolNormalForm()
4) Reduce the formula via reduceOperators()
5) Print the resuting formula if necessary via printFormula(formula_length)
6) Start the SMV model and open all output files
7) Declare variables for all of the atomic propositions
8) Call build_el_list_preorder()
9) Call functions for variable ordering
10) Close the SMV model file
11) Add SPEC statement with printFormulaVar()
12) Delete the parse tree via deleteTree() 
*****************************************************************/


int main(int argc, char **argv) {
    
    /***** Variable Declarations *****/

    /*parsing variables*/
    /*char *formula;         /*the input formula*/
    /*short paren_count;     /*for formula parsing*/
    /*struct node *current, *previous;*/
    /*char var[10];*/

    int pid;                     /*store my process ID number for use in making temp files*/
    char sout[15];               /*outfile name for the S_h characteristic function definition*/
    char tout[15];               /*outfile name for the TRANS statements*/
    char fout[15];               /*outfile name for the CTL fairness assertions*/
    char flagBuf[flagBufLength]; /*a buffer for input flags*/
    char tableauFile[50];        /*name of the smv input file representing the symbolic automaton*/
    char tableauVarFile[50];     /*name of the smv variable-order input file for the symbolic automaton*/
    char temp[50];
    
    /*KItem search;            /*a variable name to search for*/
    /*list<KItem>::iterator Kiterator;*/
       
    short i, j;                 /*iterative variables*/
    short first;

    extern node *yyparse();
    extern FILE *yyin;

  
    /* According to the documentation of rgl2, 
       
    sign=1 means that we prefer nodes that have a higher out-degree to
    selected nodes, else prefer low degree.
    
    tiebreaker=1 means that we break ties by choosing the node with the
    highest out-degree, else low-degree vertex is preferred.*/
    
    tiebreaker = 1;
    sign = 1;

    
    /*SMV model variables*/
    /*FILE *OUT;             /*SMV output file*/
    /*char *S_NOT_f;         /*ASCII name for var representing !f*/


    /*****************************************************************/
    /***** Error Checking *****/
    /*****************************************************************/

    /* warning: can do -n -n w/no complaints */

    smvFlag = 'c'; /*CadenceSMV (really C-style) comments are the default*/

    /*Check for the correct number of command-line arguments*/
    if ( (argc == 1)
	 || ( (argc == 2) && (strcmp(argv[1], "--help") == 0) ) ) {
	printUsage();
    } /*end if*/

    for (i = 1; i < argc-1; i++) {
	
	/*Error checking: make sure the flag is not too long*/
	if (strlen(argv[i]) > flagBufLength-1) {
	    fprintf(stderr, "ERROR: Expecting a flag of the form -flag; Got \'%s\'\n",
		    flagBuf);
	    printUsage();
	} /*end if*/

	strcpy(flagBuf, argv[i]); /*copy the flag into a buffer so we can parse it*/
	
	if (flagBuf[0] != '-') {
	    fprintf(stderr, "ERROR: Expecting a flag of the form -flag; Got \'%s\'\n",
		    flagBuf);
	    printUsage();
	} /*end if*/
	
	switch (flagBuf[1]) {
	    case 'b' :
	    case 'B' :
		if ((strcmp(flagBuf, "-bnf") == 0) 
		    || (strcmp(flagBuf, "-BNF") == 0)) {
		    if (useNNF == 1) {
			fprintf(stderr, "ERROR: conflicting BNF/NNF flags!\n");
			printUsage();
			exit(1);
		    } /*end if*/
		    useNNF = 0;
		} /*end if*/
		else {
		    fprintf(stderr, "Unrecognized flag1 \'%s\'\n", flagBuf);
		    printUsage();
		} /*end else*/
		break;
	    case 'c' :
	    case 'C' : /*Cadence SMV-style comments*/
		if (strlen(flagBuf) == 2) {
		    if (smvFlag != 'c') { /*because -c is the default*/
			fprintf(stderr, "ERROR: conflicting tool flags!\n");
			printUsage();
			exit(1);
		    } /*end if*/
		    smvFlag = 'c';
		    if (verbose) { fprintf(stderr, "Using CadenceSMV for the back-end\n"); }
		} /*end if*/
		else {
		    fprintf(stderr, "Unrecognized flag2 \'%s\'\n", flagBuf);
		    printUsage();
		} /*end else*/
		break;
	    case 'f' :
	    case 'F' :
		if ((strcmp(flagBuf, "-fussy") == 0) 
		    || (strcmp(flagBuf, "-FUSSY") == 0)) {
		    if (sloppy == 1) {
			fprintf(stderr, "ERROR: conflicting fussy/sloppy flags!\n");
			printUsage();
			exit(1);
		    } /*end if*/
		    sloppy = 0;
		} /*end if*/
		else {
		    fprintf(stderr, "Unrecognized flag3 \'%s\'\n", flagBuf);
		    printUsage();
		} /*end else*/
		break;
	    case 'g' :
	    case 'G' :
		if ((strcmp(flagBuf, "-gba") == 0) 
		    || (strcmp(flagBuf, "-GBA") == 0)) {

		    if (tgba) { 
			fprintf(stderr, "ERROR: conflicting flags -gba and -tgba\n");
			printUsage();
		    } /*end if*/
		    else {
			tgba = 0;
		    } /*end else*/
		} /*end if*/
		else {
		    fprintf(stderr, "Unrecognized flag4 \'%s\'\n", flagBuf);
		    printUsage();
		} /*end else*/
		break;
	    case 'l' :
	    case 'L' :
		if ((strcmp(flagBuf, "-lexm") == 0) 
		    || (strcmp(flagBuf, "-LEXM") == 0)) {
		    if (varOrder != 'z') {
			fprintf(stderr, "ERROR: conflicting variable ordering flags!\n");
			printUsage();
			exit(1);
		    } /*end if*/
		    varOrder = 'x';
		} /*end if*/
		else if ((strcmp(flagBuf, "-lexp") == 0) 
		    || (strcmp(flagBuf, "-LEXP") == 0)) {
		    if (varOrder != 'z') {
			fprintf(stderr, "ERROR: conflicting variable ordering flags!\n");
			printUsage();
			exit(1);
		    } /*end if*/
		    varOrder = 'p';
		} /*end if*/
		else if ((strcmp(flagBuf, "-linear") == 0) 
		    || (strcmp(flagBuf, "-LINEAR") == 0)) {
		    if (varOrder != 'z') {
			fprintf(stderr, "ERROR: conflicting variable ordering flags!\n");
			printUsage();
			exit(1);
		    } /*end if*/
		    varOrder = 'l';
		} /*end if*/
		else {
		    fprintf(stderr, "Unrecognized flag5 \'%s\'\n", flagBuf);
		    printUsage();
		} /*end else*/
		break;
	    case 'm' :
	    case 'M' :
		if ((strcmp(flagBuf, "-mcs") == 0) 
		    || (strcmp(flagBuf, "-MCS") == 0)) {
		    if (varOrder != 'z') {
			fprintf(stderr, "ERROR: conflicting variable ordering flags!\n");
			printUsage();
			exit(1);
		    } /*end if*/
		    varOrder = 'm';
		} /*end if*/
		else if ((strcmp(flagBuf, "-max") == 0) 
		    || (strcmp(flagBuf, "-MAX") == 0)) {
		    if (mcs_start_node != MAX) {
			fprintf(stderr, "ERROR: conflicting MCS initial node flags!\n");
			printUsage();
			exit(1);
		    } /*end if*/
		    mcs_start_node = MAX;
		} /*end if*/
		else if ((strcmp(flagBuf, "-min") == 0) 
		    || (strcmp(flagBuf, "-MIN") == 0)) {
		    if (mcs_start_node != MAX) {
			fprintf(stderr, "ERROR: conflicting MCS initial node flags!\n");
			printUsage();
			exit(1);
		    } /*end if*/
		    mcs_start_node = MIN;
		} /*end if*/
		else {
		    fprintf(stderr, "Unrecognized flag6 \'%s\'\n", flagBuf);
		    printUsage();
		} /*end else*/
		break;
	    case 'n' :
	    case 'N' : 
		if ((strcmp(flagBuf, "-nnf") == 0) 
		    || (strcmp(flagBuf, "-NNF") == 0)) {
		    useNNF = 1;
		} /*end if*/
		else if (strlen(flagBuf) == 2) { /*NuSMV-style comments*/
		    smvFlag = 'n';
		    break; 
		} /*end if*/
		else {
		    fprintf(stderr, "Unrecognized flag7 \'%s\'\n", flagBuf);
		    printUsage();
		} /*end else*/
		break;
	    case 'p' :
	    case 'P' :
		if ((strcmp(flagBuf, "-pbnf") == 0) 
		    || (strcmp(flagBuf, "-PBNF") == 0)) {
		    printBNF = 1;
		} /*end if*/
		else if ((strcmp(flagBuf, "-pnnf") == 0) 
		    || (strcmp(flagBuf, "-PNNF") == 0)) {
		    printNNF = 1;
		} /*end if*/
		else if ((strcmp(flagBuf, "-pnor") == 0) 
		    || (strcmp(flagBuf, "-PNOR") == 0)) {
		    printNoR = 1;
		} /*end if*/
		else {
		    fprintf(stderr, "Unrecognized flag8 \'%s\'\n", flagBuf);
		    printUsage();
		} /*end else*/
		break;
	    case 'r' :
	    case 'R' : /*reverse chosen variable order*/
		if ((strcmp(flagBuf, "-reverse") == 0) 
		    || (strcmp(flagBuf, "-REVERSE") == 0)) {
		    reverseOrder = 1;
		} /*end if*/
		else if ((strcmp(flagBuf, "-random") == 0) 
			 || (strcmp(flagBuf, "-RANDOM") == 0)) {
		    if (mcs_start_node != MAX) {
			fprintf(stderr, "ERROR: conflicting MCS initial node flags!\n");
			printUsage();
			exit(1);
		    } /*end if*/
		    mcs_start_node = RANDOM;
		} /*end if*/
		else {
		    fprintf(stderr, "Unrecognized flag9 \'%s\'\n", flagBuf);
		    printUsage();
		} /*end else*/
		break;
	    case 's' :
	    case 'S' :
		if ((strcmp(flagBuf, "-sloppy") == 0) 
		    || (strcmp(flagBuf, "-SLOPPY") == 0)) {
		    sloppy = 1;
		} /*end if*/
		else if (strlen(flagBuf) == 2) {
		    smvFlag = 's';
		} /*end if*/
		else {
		    fprintf(stderr, "Unrecognized flag10 \'%s\'\n", flagBuf);
		    printUsage();
		} /*end else*/
		break;
	    case 't' :
	    case 'T' :
		if ((strcmp(flagBuf, "-tgba") == 0) 
		    || (strcmp(flagBuf, "-TGBA") == 0)) {
		    tgba = 1;
		} /*end if*/
		else {
		    fprintf(stderr, "Unrecognized flag11 \'%s\'\n", flagBuf);
		    printUsage();
		} /*end else*/
		break;
	    case 'v' :
		if (strlen(flagBuf) == 2) {
		    verbose = 1;
		    fprintf(stderr, "Verbose mode engaged.\n");
		} /*end else*/
		else {
		    fprintf(stderr, "Unrecognized flag12 \'%s\'\n", flagBuf);
		    printUsage();
		} /*end else*/
		break;
	    case 'z' :
	    case 'Z' :
		if ((strcmp(flagBuf, "-zero") == 0) 
		    || (strcmp(flagBuf, "-ZERO") == 0)) {
		    if (mcs_start_node != MAX) {
			fprintf(stderr, "ERROR: conflicting MCS initial node flags!\n");
			printUsage();
			exit(1);
		    } /*end if*/
		    mcs_start_node = ZERO;
		} /*end if*/
		else {
		    fprintf(stderr, "Unrecognized flag13 \'%s\'\n", flagBuf);
		    printUsage();
		} /*end else*/
	    default :
		fprintf(stderr, "Unrecognized flag14 \'%s\'\n", flagBuf);
		printUsage();
	} /*end switch*/
    } /*end for*/
    /*i is argc-1, where the file is*/

    /*Just to make sure*/
    if (argc == 2) {
	i = 1; /*i is where the file is*/
    } /*end if*/


    /*Check for if sloppy == 1 and useNNF == 0, causing an error here*/
    if ((sloppy == 1) && (useNNF == 0)) {
	fprintf(stderr, "ERROR: Sloppy encoding can only be used with NNF formulas!\n");
	fprintf(stderr, "Either turn on NNF or use fussy encoding\n");
	printUsage();
	exit(0);
    } /*end if*/

    /*Check for if tgba == 1 and useNNF == 0, causing an error here*/
    if ((tgba == 1) && (useNNF == 0)) {
	fprintf(stderr, "ERROR: TGBA encoding can only be used with NNF formulas!\n");
	fprintf(stderr, "Either turn on NNF or use GBA encoding\n");
	printUsage();
	exit(0);
    } /*end if*/


    /*Check for proper use of variable ordering flags*/
    if ((reverseOrder == 1) && (varOrder == 'z')) { /*if no var ordering was chosen...*/
	fprintf(stderr, "ERROR: Reverse variable ordering can only be used with MCS, LEXM, LEXP, or Linear variable orderings!\n");
	fprintf(stderr, "Either turn off reverse ordering and use the default or select a variable ordering to reverse.\n");
	printUsage();
	exit(0);
    } /*end if*/

    /*Check for proper use of MCS initial node flags*/
    if ((varOrder != 'm') && (mcs_start_node != MAX)) {
	fprintf(stderr, "ERROR: Initial node flags can only be used with MCS variable ordering!\n");
	fprintf(stderr, "Either turn off initial node selection or select MCS variable ordering.\n");
	printUsage();
	exit(0);
	/*Note: this does not catch when MAX is specified but MCS is not since MAX is the default*/
    } /*end if*/

    /*Set the symbolic automaton file name*/
    if (smvFlag == 's') { /*SAL rejects .smv filenames, whatever the actual format*/
	sprintf(tableauFile, "tableau.sal");
    } /*end if*/
    else { /*Cadence SMV or NuSMV*/
	sprintf(tableauFile, "tableau.smv");
    } /*end else*/

    /*Set the variable order file name*/
    sprintf(tableauVarFile, "tableau.var");

    pid = getpid();
    if (verbose) {
	fprintf(stderr, "Process with pid %d is running..\n", pid);
    } /*end if*/


    /*Get the formula*/
    if (verbose) {
	fprintf(stderr, "Got formula file %s\n", argv[i]);
    } /*end if*/
    yyin = fopen(argv[i], "r");
    if (!yyin) {
	fprintf(stderr, "Could not open %s\n", argv[i]);
	exit(1);
    } /*end if*/


    /*****************************************************************/
    /***** Set up for Variable Ordering *****/
    /*****************************************************************/

    /*If we're using an rgl2 variable-ordering function, allocate the graph*/
    /*if (varOrder != 'z') {*/ //let's construct the graph no matter what
	/*Note: a graph_t is a pointer_t, which is a void *
	  alloc_graph, GP_VERTEX_SET, GP_VERTEX_MAP are all defined in rgl2/graph.h*/
	var_graph = alloc_graph(GP_VERTEX_SET|GP_VERTEX_MAP);
	/*} /*end if*/


    /*****************************************************************/
    /***** Parse the Formula *****/
    /*****************************************************************/
    
    yyparse(); /*Here is where the propositions are added to varList in yaccLTL.cc*/

    if (verbose) {
	fprintf(stderr, "Done parsing\n");
    } /*end if*/
	fprintf(stderr, "Formula parsed has %d non-temporal ops, %d X's, %d U's, %d R's, %d G's (of which %d are GF's), and %d F's, and uses %d propositions, %d TRUEs, %d FALSEs\n",
	       numNonTemporalOps, numX, numU, numR, numG, numGF, numF, numPROP, numTRUE, numFALSE);

    /*Tie up loose ends*/
    if (root == NULL) {
      fprintf (stderr, "ERROR: Empty parse tree returned\n");
	exit(1);
    } /*end if*/
    else {
	if (verbose) {
	    fprintf(stderr, "root is %s\n", root->me);
	} /*end if*/
    } /*end else*/
    root->parent = NULL;

    if (verbose) {
      fprintf(stderr, "formula length is %d\n", formula_length);

	fprintf(stderr, "root is %s\n", root->me);
	if (root->left_kid != NULL) {
	    fprintf(stderr, "root's left kid is %s\n", root->left_kid->me);
	}
	else {
	    fprintf(stderr, "root's left kid is NULL\n");
	}
	if (root->right_kid != NULL) {
	    fprintf(stderr, "root's right kid is %s\n", root->right_kid->me);
	}
	else {
	    fprintf(stderr, "root's right kid is NULL\n");
	}
       
	printFormula(formula_length);
    } /*end if*/

    reduceOperators(); /* NEED to do this BEFORE converting to NNF/BNF/etc.*/
    if (verbose) {
      fprintf(stderr, "\nFormula w/out -> and ~~:\n");
      printFormula(formula_length);
    } /*end if*/

    

    /*****************************************************************/
    /***** Normal Forms Section  *****/
    /*****************************************************************/

    /*Convert the formula to a normal form.*/
    if ((useNNF) || (printNNF)) { /*Convert formula to NNF*/
	negNormalForm();
	
	if (verbose) {
	  fprintf (stderr, "Using formula in Negation Normal Form:\n");
	} /*end if*/
    } /*end if*/
    else if (printNoR) { /*Remove all R-operators from formula*/
	NoRForm();
	
	if (verbose) {
	  fprintf (stderr, "Removed all R-operators from formula:\n");
	} /*end if*/
    } /*end if*/
    else {
	/*Convert formula to Boolean Normal Form*/
	boolNormalForm();
	
	if (verbose) {
	  fprintf (stderr, "Using formula in Boolean Normal Form:\n");
	} /*end if*/
    } /*end else*/
    
    /*reduceOperators();*/

    if ((verbose) || (printBNF) || (printNNF) || (printNoR)) {
	printFormula(formula_length);
    } /*end if*/

    if ((printBNF) || (printNNF) || (printNoR)) {
	return 0; /*we're done!*/
    } /*end if*/
    /*printTree(root);/*debug*/    

    /*****************************************************************/
    /***** Start the SMV Model *****/
    /*****************************************************************/

    OUT = fopen(tableauFile, "w");
    if (OUT == NULL) {
	fprintf(stderr, "ERROR: could not open1 %s for writing\n", tableauFile);
	exit(1);
    } /*end if*/

    if (varOrder != 'z') {
	VOUT = fopen(tableauVarFile, "w");
	if (VOUT == NULL) {
	    fprintf(stderr, "ERROR: could not open2 %s for writing\n", tableauVarFile);
	    exit(1);
	} /*end if*/
    } /*end if*/

    if (smvFlag == 's') { /*SAL*/
	fprintf(OUT, "tableau: CONTEXT =\nBEGIN\n\n");
	fprintf(OUT, "   main: MODULE =\n   BEGIN\n");
	fprintf(OUT, "%%"); /*SAL-style comments*/
    } /*end if*/
    else { /*Cadence or NuSMV*/
	fprintf(OUT, "MODULE main\n\n");
	if (smvFlag == 'c') { /*CadenceSMV-style comments*/
	    fprintf(OUT, "/*");
	} /*end if*/
	else if ((smvFlag == 'n') || (smvFlag == 'j')) { /*NuSMV-style comments*/
	    fprintf(OUT, "--");
	} /*end else if*/
	else { /*error*/
	    fprintf(stderr, "ERROR: Unrecognized SMV Flag: %s", smvFlag);
	    exit(1); /*die*/
	} /*end else*/
    } /*end else*/
    fprintf(OUT, "formula: ");
    printSubformulahuman(formula_length, root, OUT);
    if (smvFlag == 'c') { /*CadenceSMV-style comments*/
	fprintf(OUT, "*/");
    } /*end if*/
    fprintf(OUT, "\n");
    
    if (smvFlag == 'c') { /*CadenceSMV-style comments*/
	fprintf(OUT, "VAR \n   /*declare a boolean variable for each atomic proposition in f*/\n");
    } /*end if*/
    else if ((smvFlag == 'n') || (smvFlag == 'j')) { /*NuSMV-style comments*/
	fprintf(OUT, "VAR \n   -- declare a boolean variable for each atomic proposition in f\n");
    } /*end else if*/
    else { /*SAL-style comments*/
	fprintf(OUT, "     OUTPUT\n");
	fprintf(OUT, "     %%declare a boolean variable for each atomic proposition in f\n");
    } /*end else*/
    
    sprintf(sout, "stemp%d", pid);
    SOUT = fopen(sout, "w");
    if (SOUT == NULL) {
	fprintf(stderr, "ERROR: could not open temporary file %s for writing\n",
		sout);
	exit(1);
    } /*end if*/
    if (smvFlag == 'c') { /*CadenceSMV-style comments*/
	fprintf(SOUT, "DEFINE\n   /*for each S_h in the characteristic function, put a line here*/\n");    
    } /*end if*/
    else if ((smvFlag == 'n') || (smvFlag == 'j')) { /*NuSMV-style comments*/
	fprintf(SOUT, "DEFINE\n   -- for each S_h in the characteristic function, put a line here\n");    
    } /*end else if*/
    else { /*SAL-style comments*/
	fprintf(SOUT, "     DEFINITION\n");
	fprintf(SOUT, "     %%for each S_h in the characteristic function, put a line here\n");
    } /*end else*/

    sprintf(tout, "ttemp%d", pid);
    TOUT = fopen(tout, "w");
    if (TOUT == NULL) {
	fprintf(stderr, "ERROR: could not open temporary file %s for writing\n",
		tout);
	exit(1);
    } /*end if*/
    if (tgba == 0) {
	if (smvFlag == 'c') { /*CadenceSMV-style comments*/
	    fprintf(TOUT, "TRANS\n   /*for each (X g) in el_list, generate a line here*/\n");
	} /*end if*/
	else if ((smvFlag == 'n') || (smvFlag == 'j')) { /*NuSMV-style comments*/
	    fprintf(TOUT, "TRANS\n   -- for each (X g) in el_list, generate a line here\n");
	} /*end else if*/
	else { /*SAL-style comments*/
	    fprintf(TOUT, "     TRANSITION\n     %%for each (X g) in el_list, generate a line here\n");
	} /*end else*/
    } /*end if*/
    else { /*tgba*/
	if (smvFlag == 'c') { /*CadenceSMV-style comments*/
	    fprintf(TOUT, "TRANS\n   /*for each EL_var in el_list, generate a line here*/\n");
	} /*end if*/
	else if ((smvFlag == 'n') || (smvFlag == 'j')) { /*NuSMV-style comments*/
	    fprintf(TOUT, "TRANS\n   -- for each EL_var in el_list, generate a line here\n");
	} /*end else if*/
	else { /*SAL-style comments*/
	    fprintf(TOUT, "     TRANSITION\n     %%for each EL_var in el_list, generate a line here\n");
	} /*end else*/
    } /*end else*/

    sprintf(fout, "ftemp%d", pid);
    FOUT = fopen(fout, "w");
    if (FOUT == NULL) {
	fprintf(stderr, "ERROR: could not open temporary file %s for writing\n",
		fout);
	exit(1);
    } /*end if*/


    /*****************************************************************/
    /***** Traverse the Parse Tree *****/
    /*****************************************************************/

    /* First, get a list of the (atomic proposition) variables */
    list<KItem> tmp = varList.getItems(); /*assign to tmp a deep copy of varList*/

    if (verbose == 1) {
	fprintf(stderr, "Looping through a list of %d leaf vars...\n", tmp.size());
    } /*end if*/
    
    first = 1; /*flag: is this the first time through the loop?*/
    while (!tmp.empty()) {
        KItem var = tmp.front();
        tmp.pop_front();
	
	/*Print a line in the SMV model*/
	if (smvFlag == 's') { 
	    if (!first) { fprintf(OUT, ",\n"); }
	    else { first = 0; }
	    fprintf(OUT, "       %s : boolean", var.getName().c_str() );
	} /*end if*/
	else {
	    fprintf(OUT, "%s : boolean;\n", var.getName().c_str() );
	} /*end else*/
	
    } /*end while*/

    if (verbose == 1) {
	fprintf(stderr, "There are %d atomic propositions in the formula.\n", varList.size());
    } /*end if*/
	

    fprintf(OUT, "\n\n"); /*add some space to the SMV model file*/

    /* build_el_list_inorder();*/
    if (varOrder != 'z') {
	if (verbose) {
	    fprintf(stderr, "\n-------Before Clear------------\n");/*debug*/    
	    printTree(root); fprintf(stderr, "\n-------Before Clear------------\n");/*debug*/    
	} /*end if*/
	varList.clear(); /*clear out list for variable ordering*/
	if (verbose) {
	    fprintf(stderr, "\n--------After Clear-----------\n");/*debug*/    
	    printTree(root); fprintf(stderr, "\n--------After Clear-----------\n");/*debug*/    
	} /*end if*/
    } /*end if*/
    build_el_list_preorder(); /*Needed for variable ordering capabilities.
				Also, record each node's temporal descendants.*/

    if ((varOrder != 'z') && (verbose)) {
	printTree(root); fprintf(stderr, "\n-------------------\n");/*debug*/    
    } /*end if*/


    /*****************************************************************/
    /***** Call Functions for Variable Ordering *****/
    /*****************************************************************/

    if (varOrder != 'z') { /*if we're doing variable ordering, complete this*/
	if (verbose == 1) {
	    fprintf(stderr, "Now we have a list of %d variables.\n", varList.size());
	} /*end if*/
	
	/*Allocate the order array*/
	order_array = (int*) malloc (varList.size() * sizeof(int));

	switch(varOrder) {
	    case 'l' : /*Linear order*/
		linear_order();
		break;
	    case 'm' : /*MCS order*/
		mcs_order();
		break;
	    case 'p' : /*LEXP order*/
		lexp_order();
		break;
	    case 'x' : /*LEXM order*/
		lexm_order();
		break;
	    default : 
		fprintf(stderr, "ERROR: Unrecognized variable order \'%s\'\n", varOrder);
		exit(1);
	} /*end switch*/
	
	if (reverseOrder == 1) {
	    reverseOrderArray();
	} /*end if*/
	
	/*print the variable ordering to the output file*/
	for (i = 0; i < varList.size(); i++) {
	    j = order_array[i];
	    if (((string)(varList.findName(j)))[0] == '_') {
	      fprintf(VOUT, "EL%s\n", varList.findName(j).c_str());
	    } /*end if*/
	    else {
	      fprintf(VOUT, "%s\n", varList.findName(j).c_str());
	    } /*end else*/
	} /*end for*/

    } /*end if*/

    fprintf(OUT, "\n\n");
    fclose(OUT); /*close the SMV model file*/
    fprintf(SOUT, "\n\n");
    fclose(SOUT);
    fprintf(TOUT, "\n\n");
    fclose(TOUT);

    /*Tableaux must always have a FAIR statement*/
    if (fairnum == 0) { /*avoid an empty FAIRNESS statement semantics error*/
	if (smvFlag == 's') { /*SAL*/
	    fprintf(FOUT, "\n\n     fairness%d: TRUE\n", fairnum);
	} /*end if SAL*/
		
	/*Cadence SMV or NuSMV*/
	else if (smvFlag == 'n') { /*NuSMV*/
	  /*fprintf(FOUT, "\nJUSTICE   1\n"); I think this is NuSMV v2.4.3 and it's TRUE in 2.5.2*/
	  fprintf(FOUT, "\nJUSTICE   TRUE\n"); 
	} /*end if*/

	else if (smvFlag == 'c') {/*Cadence SMV*/
	    fprintf(FOUT, "\nFAIRNESS   TRUE\n");
	} /*end if Cadence SMV*/
	fairnum++;
    } /*end if*/

    fprintf(FOUT, "\n\n");
    fclose(FOUT);
    
    sprintf(temp, "cat %s >> %s; rm %s", sout, tableauFile, sout);
    system(temp);

    if (tgba) {fprintf (stderr, "WARNING: empty or incomplete TRANS definition\n");}
    if (nextOpPresent || (tgba && root->right_kid != NULL)) { /*avoid an empty TRANS statement syntax error*/
	sprintf(temp, "cat %s >> %s; rm %s", tout, tableauFile, tout);
	system(temp);
    } /*end if*/
    else { /*clean up anyway*/
	sprintf(temp, "rm %s", tout);
	system(temp);
    } /*end else*/

    sprintf(temp, "cat %s >> %s; rm %s", fout, tableauFile, fout);
    system(temp);

    /*End with a SPEC statement*/
    OUT = fopen(tableauFile, "a");
    if (OUT == NULL) {
	fprintf(stderr, "ERROR: could not open %s for appending\n", 
		tableauFile);
	exit(1);
    } /*end if*/

	if (smvFlag == 's') { 
	    fprintf(OUT, "   END %%main module\n\n"); /*end the main module*/
	    fprintf(OUT, "   spec: THEOREM main |- NOT(");  /*indent SAL module*/
	} /*end if SAL*/
	else { /*CadenceSMV or NuSMV*/
	    fprintf(OUT, "SPEC       !(");
	} /*end else*/
	printFormulaVar();
	
	if (smvFlag == 's') { /*SAL*/
	    fprintf(OUT, " AND EG TRUE)\n\n\n");
	    fprintf(OUT, "END %%tableau context\n");    /*end the tableau context*/
	} /*end if*/
	else { /*CadenceSMV or NuSMV*/
	    fprintf(OUT, " & EG TRUE)\n\n\n");
	} /*end else*/

    fclose(OUT); /*close the SMV model file*/
    if (varOrder != 'z') {
	fclose(VOUT); /*close the SMV variable order file*/
    } /*end if*/

    sprintf(temp, "cat %s; rm %s", tableauFile, tableauFile);
    system(temp);

    /*Delete parse tree here*/
    deleteTree();

    return 0;
} /*end main*/
