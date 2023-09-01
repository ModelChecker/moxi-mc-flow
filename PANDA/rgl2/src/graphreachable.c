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


#include "graph.h"
#include "graphops.h"
#include "set.h"

set_t
graph_forward_reachable_set(graph_t g, int init, vertex_predicate pred, pointer_t ptr)
{
  set_t reached = alloc_set(0);
  set_t new_vertices = alloc_set(0);
  set_t neighbors;
  int size_neighbors;
  int j;
  put_set(reached, init);
  put_set(new_vertices, init);
  while (size_set(new_vertices)>0) {
    neighbors = out_edges_graph(g, new_vertices[0]);
    remove_set(new_vertices, new_vertices[0]);
    size_neighbors = size_set(neighbors);
    for (j=0;j<size_neighbors;j++) {
      if (contains_set(reached, neighbors[j])) continue;
      if (pred != NULL)
	if (!(pred(g, ptr, neighbors[j]))) continue;
      reached = put_set(reached, neighbors[j]);
      new_vertices = put_set(new_vertices, neighbors[j]);
    }
  }
  free_set(new_vertices);
  return reached;
}

set_t
graph_backward_reachable_set(graph_t g, int init, vertex_predicate pred, pointer_t ptr)
{
  set_t reached = alloc_set(0);
  set_t new_vertices = alloc_set(0);
  set_t neighbors;
  int size_neighbors;
  int j;
  put_set(reached, init);
  put_set(new_vertices, init);
  while (size_set(new_vertices)>0) {
    neighbors = in_edges_graph(g, new_vertices[0]);
    remove_set(new_vertices, new_vertices[0]);
    size_neighbors = size_set(neighbors);
    for (j=0;j<size_neighbors;j++) {
      if (contains_set(reached, neighbors[j])) continue;
      if (pred != NULL)
	if (!(pred(g, ptr, neighbors[j]))) continue;
      reached = put_set(reached, neighbors[j]);
      new_vertices = put_set(new_vertices, neighbors[j]);
    }
  }
  free_set(new_vertices);
  return reached;
}

boolean_t
graph_forward_is_reachable(graph_t g, int init, int target, vertex_predicate pred, pointer_t ptr)
{
  set_t reached = alloc_set(0);
  set_t new_vertices = alloc_set(0);
  set_t neighbors;
  int size_neighbors;
  int j;
  put_set(reached, init);
  put_set(new_vertices, init);
  while (size_set(new_vertices)>0) {
    neighbors = out_edges_graph(g, new_vertices[0]);
    remove_set(new_vertices, new_vertices[0]);
    size_neighbors = size_set(neighbors);
    for (j=0;j<size_neighbors;j++) {
      if (neighbors[j]==target) {
	free_set(new_vertices);
	free_set(reached);
	return TRUE;
      }
      if (contains_set(reached, neighbors[j])) continue;
      if (pred != NULL)
	if (!(pred(g, ptr, neighbors[j]))) continue;
      reached = put_set(reached, neighbors[j]);
      new_vertices = put_set(new_vertices, neighbors[j]);
    }
  }
  free_set(new_vertices);
  free_set(reached);
  return FALSE;
}

boolean_t
graph_backward_is_reachable(graph_t g, int init, int target, vertex_predicate pred, pointer_t ptr)
{
  set_t reached = alloc_set(0);
  set_t new_vertices = alloc_set(0);
  set_t neighbors;
  int size_neighbors;
  int j;
  put_set(reached, init);
  put_set(new_vertices, init);
  while (size_set(new_vertices)>0) {
    neighbors = in_edges_graph(g, new_vertices[0]);
    remove_set(new_vertices, new_vertices[0]);
    size_neighbors = size_set(neighbors);
    for (j=0;j<size_neighbors;j++) {
      if (neighbors[j]==target) {
	free_set(new_vertices);
	free_set(reached);
	return TRUE;
      }
      if (contains_set(reached, neighbors[j])) continue;
      if (pred != NULL)
	if (!(pred(g, ptr, neighbors[j]))) continue;
      reached = put_set(reached, neighbors[j]);
      new_vertices = put_set(new_vertices, neighbors[j]);
    }
  }
  free_set(new_vertices);
  free_set(reached);
  return FALSE;
}

