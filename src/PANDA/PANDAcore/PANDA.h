/* PANDA.h

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

/* PANDA.h

   Kristin Y. Rozier
   released: June, 2011

   Input: an LTL formula

   Output: a symbolic automaton (i.e. SMV model) of the input formula
*/

/*NOTE: For this parser, formulas MUST be enclosed within parens!!!*/

#ifndef PANDA_H
#define PANDA_H

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <ctype.h>

#include "KItem.h"
#include "KList.h"

/*Includes for Variable Ordering capabilities*/
#include "typedefs.h" /*rgl2: mcs_start_t*/
#include "graph.h"    /*rgl2: connect_graph() and alloc_graph()*/
#include "graphops.h" /*rgl2: mcs_graph()*/


/*A node in the parse tree*/
struct node {
    struct node *parent;
    char *me;
    int num; /*to use for numbering the nodes/subformulas*/
    struct node *left_kid;
    struct node *right_kid;
    bool temp_kid; /*does this node have a temporal operator as a decendant?*/
};


#ifndef ROOT
#define ROOT

/*Global Variables*/
extern struct node *root;     /*the root of the parse tree*/
extern size_t formula_length; /*the number of characters in the input formula*/
extern KList varList;         /*list of used variables to avoid repeats*/
extern graph_t var_graph;     /*rgl2-library style variable graph*/
extern int tiebreaker, sign;  /*rgl2-library flag variables*/

/*Operator Counters*/
/*  these are just for information, debugging*/
extern int numNonTemporalOps; /*how many &'s, |'s, and ->'s are in the input formula?*/
extern int numX;              /*how many X's are in the input formula?*/
extern int numU;              /*how many U's are in the input formula?*/
extern int numR;              /*how many R's are in the input formula?*/
extern int numG;              /*how many G's are in the input formula?*/
extern int numGF;             /*how many GF's are in the input formula? (These also get counted individually.)*/
extern int numF;              /*how many F's are in the input formula?*/
extern int numPROP;           /*how many times are props used in the input formula?*/
extern int numTRUE;           /*how many times is TRUE used in the input formula?*/
extern int numFALSE;          /*how many times is FALSE used in the input formula?*/

#endif


/*Required function definitions*/
void connect_graph(int from, int to);


#endif /*PANDA_H*/
