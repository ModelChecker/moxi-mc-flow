/*********************************************************************
* Software License Agreement (BSD License)
*
*  Copyright (c) 2011, Rice University.
*  All rights reserved.
*
*  Redistribution and use in source and binary forms, with or without
*  modification, are permitted provided that the following conditions
*  are met:
*
*   * Redistributions of source code must retain the above copyright
*     notice, this list of conditions and the following disclaimer.
*   * Redistributions in binary form must reproduce the above
*     copyright notice, this list of conditions and the following
*     disclaimer in the documentation and/or other materials provided
*     with the distribution.
*   * Neither the name of the Rice University nor the names of its
*     contributors may be used to endorse or promote products derived
*     from this software without specific prior written permission.
*
*  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
*  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
*  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
*  FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
*  COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
*  INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
*  BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
*  LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
*  CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
*  LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
*  ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
*  POSSIBILITY OF SUCH DAMAGE.
*********************************************************************/

/* Author: Andrew Ladd */


#include "heuristics.h"
#include "graph.h"
#include "graphops.h"

extern int tiebreaker, sign;

/**
 * Uses the rgl package to define the graph that corresponds to the
 * automaton that we are dealing with. Returns the graph.
 */
graph_t makeGraph(params_t params) {
  uint_t automaton_size = params->automaton_params->automaton_size;
  graph_t graph = alloc_graph(GP_VERTEX_SET|GP_VERTEX_MAP);
  int i, j;

  /*Build the graph using the rgl package */
  for (i = 0; i<automaton_size; i++) {
    
    connect_graph(graph, i, i);
   
    for (j = 0; j<automaton_size; j++)
      if ( isConnected(i, j, params) )
	connect_graph(graph, i, j);
  }
  
  return graph;
}





/**
 * Uses the value of the global @variable mcs_start_at to determine
 * which node should go first in the MCS heuristic.
 */
int determineMCSinitialNode(mcs_start_t mcs_start_at, params_t params) {
  
  fprintf(stderr, "Determine the initial node for %s\n", mcs_start2str(mcs_start_at));

  uint_t automaton_size = params->automaton_params->automaton_size;

  if (mcs_start_at == MIN)
    return getMinDegreeNode(params);

  else if (mcs_start_at == MAX)
    return getMaxDegreeNode(params);

  else if (mcs_start_at == ZERO)
    return 0;
  
  else if (mcs_start_at == RANDOM) 
    return rand() % automaton_size;

  else {
    fprintf(stderr, "Unknown mcs_start_at variable %d (%s)\n", 
	       mcs_start_at, mcs_start2str(mcs_start_at));
    return 0; //unreachable
  }
}



/** 
 * Reads the transition graph from A and B defined externally and
 * produces a variable order based on maximum cardinality
 * search. Using the algorithm defined in RGL.

 * @param automaton_size defined externally to be the size of the
 * automaton and thus the number of nodes in the graph.
 
 */
int* mcs_order(params_t params) {

  uint_t automaton_size = params->automaton_params->automaton_size;
  int *order_array = (int*) malloc (automaton_size * sizeof(int));
  graph_t graph = makeGraph(params);
  int i;

  /* According to the documentation of rgl2, 

  sign=1 means that we prefer nodes that have a higher out-degree to
  selected nodes, else prefer low degree.

  tiebreaker=1 means that we break ties by choosing the node with the
  highest out-degree, else low-degree vertex is preferred.*/
  
  tiebreaker = 1; /*rgl library: rgl breaks ties*/
  sign = 1; /*control the way the ordering is done, conflicts resolved*/
  int initial_node = determineMCSinitialNode(params->mcs_start_node, params);
  /*choose initial node: max out-degree, min, etc. makes almost no difference
   picking randomly is a good choice or just using the root*/
  mcs_graph(graph, initial_node, order_array); /*defined by rgl; result returned in order_array*/
  //printf("DEBUG MODE: mcs_graph() returned back to me\n");

  fprintf(stderr, "The initial node is %d\n", initial_node);
  fprintf(stderr, "The mcs order is:\n");
  for (i = 0; i<automaton_size; i++)
    fprintf(stderr, "   %d: %d\n", i, order_array[i]);
  free_graph(graph);
  return order_array;
}





/**
 * Orders the variables according to the LEXM heuristic as referenced
 * in Pan's SAT'04 paper. Uses the RGL package for the heuristic
 * implementation.
 */
int* lexm_order(params_t params) {
  uint_t automaton_size = params->automaton_params->automaton_size;
  int *order_array = (int*) malloc (automaton_size * sizeof(int));
  graph_t graph = makeGraph(params);
  
  tiebreaker = 1; 
  sign = 1;

  lexicographic_bfs_graph_min(graph, 0, order_array);
  free_graph(graph);
  return order_array;
}





/**
 * Orders the variables according to the LEXP heuristic as referenced
 * in Pan's SAT'04 paper. Uses the RGL package for the heuristic
 * implementation.
 */
int* lexp_order(params_t params) {
  uint_t automaton_size = params->automaton_params->automaton_size;

  int *order_array = (int*) malloc (automaton_size * sizeof(int));
  graph_t graph = makeGraph(params);
  

  tiebreaker = 1; 
  sign = 1;


  lexicographic_bfs_graph(graph, 0, order_array);
  free_graph(graph);
  return order_array;
}



/**
 * Orders the variables linearly. It is probably a horrible order
 * unless the model is highly linear itself.
 */
int* linear_order(params_t params) {
  uint_t automaton_size = params->automaton_params->automaton_size;
  int *order_array = (int*) malloc (automaton_size * sizeof(int));
  int i;
  
  for (i = 0; i<automaton_size; i++) 
    order_array[i] = i;
  
  return order_array;
}



/**
 * Given the array with order of the variables, reverse the
 * order. Assumes that the array has length @automaton_size, which is
 * defined externaly.
 */
void reverseOrderArray(int* order_array, params_t params) {
  uint_t automaton_size = params->automaton_params->automaton_size;
  int i;

  if (order_array == NULL)
    return;
  int* temp =  (int*) malloc (automaton_size * sizeof(int));
  for (i = 0; i<automaton_size; i++)
    temp[i] = order_array[automaton_size - i - 1];

  for (i = 0; i<automaton_size; i++)
    order_array[i] = temp[i];
  
  
  free(temp);
}




/** 
 * Returns whether the first node is connected to the second via
 * either one of the two transition matrices.
 */
bool isConnected(int n1, int n2, params_t params) {
  bool to_return = false;
  int i;

  for (i = 0; i<params->automaton_params->num_letters; i++) {
    bool** matrix = params->automaton_params->transitions[i];
    to_return = to_return || matrix[n1][n2];
  }

  
  return to_return;
}




/**
 * Returns the node in the graph that has the highest out-degree. Ties
 * are broken somewhat arbitrarily (select the first such node). 
 */
int getMaxDegreeNode(params_t params) {
  uint_t automaton_size = params->automaton_params->automaton_size;
  int maxOutDegree = 0;
  int selectedNode = 0;
  int i;

  for (i = 0; i<automaton_size; i++) {
    
    int currOutDegree = countOutDegree(i, params);
    
    if (maxOutDegree < currOutDegree) {
      maxOutDegree = currOutDegree;
      selectedNode = i;
    }
  }
  
  return selectedNode;
}




/** 
 * Calculates the out-degree of the node. Note that we are assuming
 * connectivity, not actual number of edges.
 */
int countOutDegree(int node_num, params_t params) {
  uint_t automaton_size = params->automaton_params->automaton_size;
  int outDegree = 0;
  int i;

  for (i = 0; i<automaton_size; i++)
    if (isConnected(node_num, i, params))
      outDegree ++;
  
  return outDegree;
}




/**
 * Returns the node in the graph that has the lowest out-degree. Ties
 * are broken somewhat arbitrarily (select the first such node). 
 */
int getMinDegreeNode(params_t params) {
  uint_t automaton_size = params->automaton_params->automaton_size;
  int minOutDegree = 0;
  int selectedNode = 0;
  int i;
  
  for (i = 0; i<automaton_size; i++) {
    
    int currOutDegree = countOutDegree(i, params);
    
    if (minOutDegree < currOutDegree) {
      minOutDegree = currOutDegree;
      selectedNode = i;
    }
  }
  
  return selectedNode;
}




/** from Deian's utils.c...
 * Returns the string representation of the MCS starting mode index.
 */
char* mcs_start2str(mcs_start_t mcs_start_num) {
    
  switch(mcs_start_num) {
   case MAX: return "MAX OUTDEGREE"; 
     break;
   case MIN: return "MIN OUTDEGREE"; 
     break;
   case ZERO: return "INITIAL NODE"; 
     break;
   case RANDOM: return "RANDOM NODE"; 
     break;
   default: return "** UNKNOWN STARTING NODE **";
     break;
   }
}
