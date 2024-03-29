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


#include "graphalg.h"
#include "fast_union.h"

int 
num_connected_components(graph_t g)
{
  set_t vertices = vertex_set_graph(g);
  int n = size_set(vertices);
  set_t fsets = alloc_set(SP_MAP);
  set_t csets;

  int i;
  int c;

  for (i=0; i<n; i++) 
    fsets = associate_set(fsets, vertices[i], alloc_fast_union(vertices[i]));
  
  for (i=0; i<n; i++) {
    set_t edges = out_edges_graph(g, vertices[i]);
    int m = size_set(edges);
    int j;

    fast_union_t *rep = (fast_union_t *) ith_map_set(fsets, i);

    for (j=0; j<m; j++) {
      fast_union_t *jrep = (fast_union_t *) mapsto_set(fsets, edges[j]);

      union_fast_union(rep, jrep);
    }
  }

  csets = alloc_set(0);
  
  for (i=0; i<n; i++) {
    fast_union_t *rep = (fast_union_t *) ith_map_set(fsets, i);

    int repr = representative_fast_union(rep);

    csets = put_set(csets, repr);
  }
  
  c = size_set(csets);

  for (i=0; i<n; i++) {
    fast_union_t *rep = (fast_union_t *) ith_map_set(fsets, i);
    
    free_fast_union(rep);
  }

  free_set(csets);
  free_set(fsets);

  return c;
}
