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


#include "astar.h"
#include "fbheap.h"

static set_t cover;

typedef struct p_seg_t
{
  double cost;
  double estimate;  
  
  int vertex;

  struct p_seg_t *prev;
} p_seg_t;


static int 
cmp_path(pointer_t data, int a, int b)
{
  p_seg_t *pa = (p_seg_t *) mapsto_set(cover, a);
  p_seg_t *pb = (p_seg_t *) mapsto_set(cover, b);

  if (pa->estimate < pb->estimate) return -1;
  else if (pa->estimate > pb->estimate) return 1;
  else return 0;
}

/**
 * Computes a path between two vertices in a graph using the A-star heuristic.  The 
 * distance estimate needs to be metric and needs to be conservative.
 *
 * @param graph a (directed?) graph over a set of keys.
 * @param start the starting vertex for the path.
 * @param finish the finish vertex for the path.
 * @param cost_fn a cost function for the graph.
 * @param estimate_fn a distance metric for A-star.
 * @param cost_data the pointer passed to the cost function when its called.
 * @param estimate_data the pointer passed to the distance function when its called.
 * @param len will be set to the length of the final path or zero if no path.
 * @param path will be set to an array of length len or NULL if no path.
 *
 * @return total path cost.
 */

double 
get_shortest_path_astar(graph_t graph, int start, int finish, 
			       cost_fn_t cost_fn, estimate_fn_t estimate_fn,
			       pointer_t cost_data, pointer_t estimate_data,
			       int *len, int **path)
{
  p_seg_t *pinit = (p_seg_t *) malloc(sizeof(p_seg_t));
  fbheap_t heap = alloc_fbheap(cmp_path, NULL);

  pointer_t *maptable;
  int m, i;

  cover = alloc_set(SP_MAP);

  pinit->cost = 0.0;
  pinit->estimate = estimate_fn(estimate_data, start);
  pinit->vertex = start;
  pinit->prev = NIL;
  
  cover = associate_set(cover, start, pinit);
  heap = put_fbheap(heap, start);

  while (size_fbheap(heap) > 0) {
    int key = extract_fbheap(heap);
    p_seg_t *part = (p_seg_t *) mapsto_set(cover, key);
    set_t edges;
    
    if (part->vertex == finish) {  // found the path
      int n = 0;
      p_seg_t *curr = part;

      double total = part->cost;

      while (curr) { n++; curr = curr->prev; }
      
      curr = part;
      *path = (int *) malloc(sizeof(int) * n);
      *len = n;
      
      for (i=0; i<n; i++) {
	(*path)[n - i - 1] = curr->vertex;
	curr = curr->prev;
      }
      
      maptable = maptable_set(cover);
      m = size_set(cover);

      for (i=0; i<m; i++) free(maptable[i]);

      free_set(cover);
      free_fbheap(heap);

      return total;
    }

    edges = out_edges_graph(graph, key);

    if (edges) m = size_set(edges);
    else m = 0;
    
    for (i=0; i<m; i++) {
      if (contains_set(cover, edges[i]) == FALSE) {
	p_seg_t *np = (p_seg_t *) malloc(sizeof(p_seg_t));
	
	np->cost = part->cost + cost_fn(cost_data, key, edges[i]);
	np->estimate = np->cost + estimate_fn(estimate_data, edges[i]);
	np->vertex = edges[i];
	np->prev = part;

	cover = associate_set(cover, edges[i], np);
	heap = put_fbheap(heap, edges[i]);	
      }
    }    
  }

  maptable = maptable_set(cover);
  m = size_set(cover);

  for (i=0; i<m; i++) free(maptable[i]);
  
  free_set(cover);
  free_fbheap(heap);

  *len = 0;
  *path = NULL;

  return 0.0;  
}
