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


#ifndef _____RGL_GRAPHOPS___H___
#define _____RGL_GRAPHOPS___H___

#include "graph.h"
#include "set.h"

BEGIN_C_DECL

#define LEXP 0x01
#define LEXM 0x02
#define MCS 0x04
#define FASTSEED 0x10
#define MCSSEED 0x20

typedef boolean_t (*vertex_predicate)(graph_t g, pointer_t context, int vertex);

set_t graph_forward_reachable_set(graph_t g, int init, vertex_predicate pred, pointer_t ptr);
set_t graph_backward_reachable_set(graph_t g, int init, vertex_predicate pred, pointer_t ptr);
boolean_t graph_forward_is_reachable(graph_t g, int init, int target, vertex_predicate pred, pointer_t ptr);
boolean_t graph_backward_is_reachable(graph_t g, int init, int target, vertex_predicate pred, pointer_t ptr);

int triangulate_graph(graph_t g, int *elim);
int triangulate_graph_nodisconnect(graph_t g, int *elim);
void lexicographic_bfs_graph(graph_t g, int seed, int *elim);
void lexicographic_bfs_graph_min(graph_t g, int seed, int *elim);
void mcs_graph(graph_t g, int seed, int *elim);
void min_induced_width_graph(graph_t g, int *elim);
void min_fill_graph(graph_t g, int *elim);

graph_t build_tree_decomposition_graph(graph_t g, int *elim);
void reroot_tree_decomposition_graph(graph_t td, set_t target, int *elim);

void build_vo_graph(graph_t g, int options, int *elim);
void mcs_graph_seed(graph_t g, set_t seed, int *elim);
void mcs_graph_layered(graph_t g, int *elim);

void sift_graph_width(graph_t g, int count, int *elim);




void lexicographic_bfs_graph2(graph_t g, int *elim,int* freevariables, int numoffree);
void lexicographic_bfs_graph_min2(graph_t g, int *elim,int* freevariables, int numoffree);
void mcs_graph2(graph_t g, int *elim,int* freevariables, int numoffree);
void min_induced_width_graph2(graph_t g, int *elim,int* freevariables, int numoffree);
void min_fill_graph2(graph_t g, int *elim,int* freevariables, int numoffree);


END_C_DECL

#endif
