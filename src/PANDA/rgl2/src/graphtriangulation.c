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


#include "set.h"
#include "graph.h"
#include "graphops.h"
#include "lexset.h"
#include "bheap.h"
#include "fast_union.h"

/**
 * Triangulates a graph according to a elimination scheme
 *
 * @param g a graph.
 * @param elim the order of vertices to be eliminated.
 *
 * @return The tree width of the graph
 */

int
triangulate_graph(graph_t g, int *elim)
{
  int vertices = num_vertices_graph(g);
  set_t processed_vertices;
  set_t neighbors;
  set_t added_edges;
  int size_neighbors;
  int tree_width, i, j, k;
  
  tree_width = 0;
  processed_vertices = alloc_set(0);
  added_edges = alloc_set(0);

  for (i=0;i<vertices;i++) {
    processed_vertices = put_set(processed_vertices, elim[i]);

    neighbors = subtract_set(out_edges_graph(g, elim[i]), processed_vertices);
    size_neighbors = size_set(neighbors);
    tree_width = (tree_width>size_neighbors?tree_width:size_neighbors);

    for (j=0;j<size_neighbors;j++) {
      for (k=j+1;k<size_neighbors;k++) {
	if (!has_edge_graph(g, neighbors[j], neighbors[k])) {
	  connect_graph(g, neighbors[j], neighbors[k]);
	  added_edges = put_set(added_edges, neighbors[j]*vertices+neighbors[k]);
	}
      }
    }
    free_set(neighbors);
  }
  size_neighbors = size_set(added_edges);
  for (i=0;i<size_neighbors;i++) {
    j = added_edges[i]/vertices;
    k = added_edges[i]-j*vertices;
    disconnect_graph(g, j, k);
  }
  free_set(added_edges);    
  free_set(processed_vertices);
  return tree_width;
}

int
triangulate_graph_nodisconnect(graph_t g, int *elim)
{
  int vertices = num_vertices_graph(g);
  set_t processed_vertices;
  set_t neighbors;
  int size_neighbors;
  int tree_width, i, j, k;
  
  tree_width = 0;
  processed_vertices = alloc_set(0);

  for (i=0;i<vertices;i++) {
    processed_vertices = put_set(processed_vertices, elim[i]);

    neighbors = subtract_set(out_edges_graph(g, elim[i]), processed_vertices);
    size_neighbors = size_set(neighbors);
    tree_width = (tree_width>size_neighbors?tree_width:size_neighbors);

    for (j=0;j<size_neighbors;j++) {
      for (k=j+1;k<size_neighbors;k++) {
	if (!has_edge_graph(g, neighbors[j], neighbors[k])) {
	  connect_graph(g, neighbors[j], neighbors[k]);
	}
      }
    }
    free_set(neighbors);
  }
  free_set(processed_vertices);
  return tree_width;
}

graph_t
build_tree_decomposition_graph(graph_t g, int *elim)
{
  int vertices = num_vertices_graph(g);
  int i,j,k,size_neighbors;
  set_t s,s2,neighbors,added_edges=alloc_set(0);
  set_t processed_vertices = alloc_set(0);
  graph_t td = alloc_graph(GP_VERTEX_SET|GP_VERTEX_MAP);
  set_t disconnected_vertices = alloc_set(0);
  fast_union_t **fu = malloc(sizeof(fast_union_t *)*vertices);
  for (i=0;i<vertices;i++) {
    //    printf("var = %d\n", elim[i]);
    fu[i] = alloc_fast_union(i);
    processed_vertices = put_set(processed_vertices, elim[i]);
    neighbors = subtract_set(out_edges_graph(g, elim[i]), processed_vertices);
    size_neighbors = size_set(neighbors);
    for (j=0;j<size_neighbors;j++) {
      for (k=j+1;k<size_neighbors;k++) {
	if (!has_edge_graph(g, neighbors[j], neighbors[k])) {
	  connect_graph(g, neighbors[j], neighbors[k]);
	  added_edges = put_set(added_edges, neighbors[j]*vertices+neighbors[k]);
	}
      }
    }
    s = put_set(neighbors, elim[i]);
    associate_vertex_graph(td, i, (pointer_t)s);
    for (j=i-1;j>=0;j--) {
      s2 = (set_t)mapsto_vertex_graph(td, j);
      if (contains_set(s2, elim[i])) {
	//	printf("connect1: %d %d\n", i, j);
	connect_graph(td,i,j);
	union_fast_union(fu[i], fu[j]);
	break;
      }
    }
    if ((i>0)&&(j<0)) {
      //printf("%d is not connected\n", i);
      disconnected_vertices = put_set(disconnected_vertices, i);
    }
    for (j--;j>=0;j--) {
      if (representative_fast_union(fu[i])!=representative_fast_union(fu[j])) {
	s2 = (set_t)mapsto_vertex_graph(td, j);
	if (contains_set(s2, elim[i])) {
	  //  printf("connect2: %d %d\n", i, j);
	  connect_graph(td,i,j);
	  remove_set(disconnected_vertices,j);
	  union_fast_union(fu[i], fu[j]);
	}
      }
    }
  }
  for (i=0;i<size_set(disconnected_vertices);i++) {
    //  printf("connect3: %d %d\n", 0, disconnected_vertices[i]);
    connect_graph(td, 0, disconnected_vertices[i]);
  }
  free_set(disconnected_vertices);

  size_neighbors = size_set(added_edges);
  for (i=0;i<size_neighbors;i++) {
    j = added_edges[i]/vertices;
    k = added_edges[i]-j*vertices;
    disconnect_graph(g, j, k);
  }

  printf("vertices in tree decomposition = %d\n", num_vertices_graph(td));
  printf("Processed vertices = %d\n", size_set(processed_vertices));

  for (i=0;i<vertices;i++) {
    free_fast_union(fu[i]);
  }
  free(fu);
  
  free_set(added_edges);    
  free_set(processed_vertices);
  return td;
}

void traverse_tree_add_vertices_internal(graph_t td, int root, set_t *visited, set_t *pv, int *elim)
{
  int i;
  set_t s = (set_t)mapsto_vertex_graph(td, root);
  int vertices = num_vertices_graph(td);
  int size = size_set(s);
  int size_pv;
  *visited = put_set(*visited, root);
  for (i=0;i<size;i++) {
    if (contains_set(*pv, s[i]))
      continue;
    size_pv = size_set(*pv);
    elim[vertices-size_pv-1] = s[i];
    *pv = put_set(*pv, s[i]);
  }
  s = out_edges_graph(td, root);
  s = subtract_set(s, *visited);
  size = size_set(s);
  for (i=0;i<size;i++) {
    traverse_tree_add_vertices_internal(td, s[i], visited, pv, elim);
  }
}

void 
reroot_tree_decomposition_graph(graph_t td, set_t target, int *elim)
{
  int i,j;
  int root = -1;
  int vertices = num_vertices_graph(td);
  int minsize = vertices;
  set_t s,s2,processed_vertices = alloc_set(0), visited = alloc_set(0);
  for (i=0;i<vertices;i++) {
    s = (set_t)mapsto_vertex_graph(td, i);
    s2 = subtract_set(target, s);
    if (size_set(s2)>0) {
      free_set(s2);
      continue;
    }
    free_set(s2);
    s2 = subtract_set(s, target);
    if (size_set(s2)<minsize) {
      minsize = size_set(s2);
      root = i;
    }
    free_set(s2);
  }
  assert(root != -1);
  for (i=vertices-1,j=0;j<size_set(target);i--,j++) {
    elim[i] = target[j];
    processed_vertices = put_set(processed_vertices, target[j]);
  }
  
  traverse_tree_add_vertices_internal(td, root, &visited, &processed_vertices, elim);
  printf("visited = %d, added = %d, should be %d\n", size_set(visited), size_set(processed_vertices), vertices);
  assert(size_set(processed_vertices)==vertices);
  free_set(processed_vertices);
}

int tiebreaker = 1;
int sign = 1;

/*
  The bheap implementation makes the least element to appear at the top, assuming the compare(i,j)>0 iff i>j.
  We need the greatest tagged element so the result is negated by default, unless sign=-1.
  For tiebreakers, if tiebreaker = 1, then high degree vertex is preferred, else low degree is preferred.
 */

int compare_graph_lexset(pointer_t p, int i, int j)
{
  graph_t g = (graph_t)p;
  lex_t l1, l2;
  int res;
  l1 = (lex_t)mapsto_vertex_graph(g, i);
  l2 = (lex_t)mapsto_vertex_graph(g, j);
  res = -compare_lexset(l1, l2)*sign;
  if (res != 0)
    return res;
  return tiebreaker * (size_set(out_edges_graph(g, j))-size_set(out_edges_graph(g,i)));
}

void
lexicographic_bfs_graph(graph_t g, int seed, int *elim)
{
  int size = num_vertices_graph(g);
  int i,j,size_neighbors;
  bheap_t heap;
  set_t neighbors, processed_vertices;
  lex_t work;
  processed_vertices = alloc_set(0);
  for (i=0;i<size;i++) {
    work = alloc_lexset();
    associate_vertex_graph(g, i, (pointer_t)work);
  }
  heap = alloc_bheap(compare_graph_lexset, g);
  for (i=0;i<size;i++) {
    if (i != seed)
      heap = put_bheap(heap, i);
  }
  for (i=size-1;i>=0;i--) {
    if (i == size-1) 
      elim[i] = seed;
    else
      elim[i] = extract_bheap(heap);
    processed_vertices = put_set(processed_vertices, elim[i]);
    neighbors = subtract_set(out_edges_graph(g, elim[i]), processed_vertices);
    size_neighbors = size_set(neighbors);
    for (j=0;j<size_neighbors;j++) {
      remove_bheap(heap, neighbors[j]);
      work = mapsto_vertex_graph(g, neighbors[j]);
      add_lexset(work, i);
      if (!contains_set(processed_vertices, neighbors[j]))
	heap = put_bheap(heap, neighbors[j]);
    }
  }
  for (i=0;i<size;i++) {
    work = mapsto_vertex_graph(g, i);
    free_lexset(work);
    associate_vertex_graph(g, i, (pointer_t)NULL);
  }
  free_bheap(heap);
  free_set(processed_vertices);
}

boolean_t
graph_lexset_lessthen(graph_t g,  pointer_t ref, int v)
{
  lex_t x = (lex_t) ref;
  lex_t y = (lex_t)mapsto_vertex_graph(g, v);
  if (compare_lexset(x,y)<0)
    return TRUE;
  else
    return FALSE;
}

void
lexicographic_bfs_graph_min(graph_t g, int seed, int *elim)
{
  int size = num_vertices_graph(g);
  int i,j,size_neighbors;
  bheap_t heap;
  set_t neighbors, processed_vertices;
  lex_t work;
  processed_vertices = alloc_set(0);
  for (i=0;i<size;i++) {
    work = alloc_lexset();
    associate_vertex_graph(g, i, (pointer_t)work);
  }
  heap = alloc_bheap(compare_graph_lexset, g);
  for (i=0;i<size;i++) {
    if (i != seed)
      heap = put_bheap(heap, i);
  }
  for (i=size-1;i>=0;i--) {
    if (i == size-1) 
      elim[i] = seed;
    else
      elim[i] = extract_bheap(heap);
    processed_vertices = put_set(processed_vertices, elim[i]);
    neighbors = subtract_set(out_edges_graph(g, elim[i]), processed_vertices);
    size_neighbors = size_set(neighbors);
    for (j=0;j<size_neighbors;j++) {
      remove_bheap(heap, neighbors[j]);
      work = mapsto_vertex_graph(g, neighbors[j]);
      add_lexset(work, i);
      if (!contains_set(processed_vertices, neighbors[j]))
	heap = put_bheap(heap, neighbors[j]);
    }
    neighbors = subtract_set(vertex_set_graph(g), processed_vertices);
    size_neighbors = size_set(neighbors);
    for (j=0;j<size_neighbors;j++) {
      work = mapsto_vertex_graph(g, neighbors[j]);
      if (contains_lexset(work, elim[i])) continue;
      if (graph_backward_is_reachable(g, neighbors[j], elim[i], graph_lexset_lessthen, (pointer_t)work)) {
	remove_bheap(heap, neighbors[j]);
	add_lexset(work, i);
	if (!contains_set(processed_vertices, neighbors[j]))
	  heap = put_bheap(heap, neighbors[j]);
      }
    }
  }
  for (i=0;i<size;i++) {
    work = mapsto_vertex_graph(g, i);
    free_lexset(work);
    associate_vertex_graph(g, i, (pointer_t)NULL);
  }
  free_bheap(heap);
  free_set(processed_vertices);
}

/* if sign = 1, prefer high degree to previously chosen vertex, else prefer low degree. */

int compare_graph_int(pointer_t p, int i, int j)
{
  graph_t g = (graph_t)p;
  int t1, t2, res;
  t1 = (int)mapsto_vertex_graph(g, i);
  t2 = (int)mapsto_vertex_graph(g, j);
  res = sign * (t2 - t1);
  if (res != 0)
    return res;
  return tiebreaker * (size_set(out_edges_graph(g, j))-size_set(out_edges_graph(g,i)));
}

int compare_graph_level_int(pointer_t p, int i, int j)
{
  graph_t g = (graph_t)p;
  unsigned int t1, t2, d1, d2, w1, w2, res;
  t1 = (unsigned int)mapsto_vertex_graph(g, i);
  t2 = (unsigned int)mapsto_vertex_graph(g, j);
  d1 = t1>>16;
  d2 = t2>>16;
  if (d2>d1) return 1;
  if (d1>d2) return -1;
  w1 = t1&0xffff;
  w2 = t2&0xffff;
  res = sign * (w2 - w1);
  if (res != 0)
    return res;
  return tiebreaker * (size_set(out_edges_graph(g, j))-size_set(out_edges_graph(g,i)));
}

void min_induced_width_graph(graph_t g, int *elim)
{
  int size = num_vertices_graph(g);
  int i,j,k,size_neighbors;
  bheap_t heap;
  set_t neighbors, processed_vertices, added_edges;
  int work;
  int *neighbor_edges;
  int oldsign = sign;
  sign = -1;
  processed_vertices = alloc_set(0);
  added_edges = alloc_set(0);
  heap = alloc_bheap(compare_graph_int, g);
  for (i=0;i<size;i++) {
    associate_vertex_graph(g, i, (pointer_t)(size_set(out_edges_graph(g, i))));
    heap = put_bheap(heap, i);
  }
  neighbor_edges = (int *)alloca(sizeof(int)*size);
  for (i=0;i<size;i++) {
    elim[i] = extract_bheap(heap);
    processed_vertices = put_set(processed_vertices, elim[i]);
    neighbors = subtract_set(out_edges_graph(g, elim[i]), processed_vertices);
    size_neighbors = size_set(neighbors);
    for (j=0;j<size_neighbors;j++)
      neighbor_edges[j] = -1;
    for (j=0;j<size_neighbors;j++) {
      for (k=j+1;k<size_neighbors;k++) {
	if (!has_edge_graph(g, neighbors[j], neighbors[k])) {
	  connect_graph(g, neighbors[j], neighbors[k]);
	  added_edges = put_set(added_edges, neighbors[j]*size+neighbors[k]);
	  neighbor_edges[j]++;
	  neighbor_edges[k]++;
	}
      }
    }
    for (j=0;j<size_neighbors;j++) {
      remove_bheap(heap, neighbors[j]);
      work = (int)mapsto_vertex_graph(g, neighbors[j]);
      work += neighbor_edges[j];
      associate_vertex_graph(g, neighbors[j], (pointer_t)work);
      heap = put_bheap(heap, neighbors[j]);
    }
    free_set(neighbors);
  }
  for (i=0;i<size;i++) {
    associate_vertex_graph(g, i, (pointer_t)NULL);
  }
  size_neighbors = size_set(added_edges);
  for (i=0;i<size_neighbors;i++) {
    j = added_edges[i]/size;
    k = added_edges[i]-j*size;
    disconnect_graph(g, j, k);
  }
  free_set(added_edges);    
  free_set(processed_vertices);
  free_bheap(heap);
  sign = oldsign;
}

int get_fill_size(graph_t g, set_t neighbors)
{
  int i,f;
  int size = size_set(neighbors);
  set_t work;
  f = 0;
  for (i=0;i<size;i++) {
    work = intersect_set(out_edges_graph(g, neighbors[i]), neighbors);
    f += (size - size_set(work) - 1);
    free_set(work);
  }
  return f;
}

void min_fill_graph(graph_t g, int *elim)
{
  int size = num_vertices_graph(g);
  int i,j,k,size_neighbors;
  bheap_t heap;
  set_t neighbors, processed_vertices, added_edges;
  set_t n2;
  int work;
  int oldsign = sign;
  sign = -1;
  processed_vertices = alloc_set(0);
  added_edges = alloc_set(0);
  heap = alloc_bheap(compare_graph_int, g);
  for (i=0;i<size;i++) {
    associate_vertex_graph(g, i, (pointer_t)get_fill_size(g, out_edges_graph(g, i)));
    heap = put_bheap(heap, i);
  }
  for (i=0;i<size;i++) {
    elim[i] = extract_bheap(heap);
    processed_vertices = put_set(processed_vertices, elim[i]);
    neighbors = subtract_set(out_edges_graph(g, elim[i]), processed_vertices);
    size_neighbors = size_set(neighbors);
    for (j=0;j<size_neighbors;j++) {
      for (k=j+1;k<size_neighbors;k++) {
	if (!has_edge_graph(g, neighbors[j], neighbors[k])) {
	  connect_graph(g, neighbors[j], neighbors[k]);
	  added_edges = put_set(added_edges, neighbors[j]*size+neighbors[k]);
	}
      }
    }
    for (j=0;j<size_neighbors;j++) {
      remove_bheap(heap, neighbors[j]);
      n2 = subtract_set(out_edges_graph(g, neighbors[j]), processed_vertices);
      work = get_fill_size(g, n2);
      associate_vertex_graph(g, neighbors[j], (pointer_t)work);
      heap = put_bheap(heap, neighbors[j]);
    }
    free_set(neighbors);
  }
  for (i=0;i<size;i++) {
    associate_vertex_graph(g, i, (pointer_t)NULL);
  }
  size_neighbors = size_set(added_edges);
  for (i=0;i<size_neighbors;i++) {
    j = added_edges[i]/size;
    k = added_edges[i]-j*size;
    disconnect_graph(g, j, k);
  }
  free_set(added_edges);    
  free_set(processed_vertices);
  free_bheap(heap);
  sign = oldsign;
}












void
mcs_graph(graph_t g, int seed, int *elim)
{ 
  int size = num_vertices_graph(g);
  int i,j,size_neighbors;
  bheap_t heap;
  set_t neighbors, processed_vertices;
  int work;
  processed_vertices = alloc_set(0);
  heap = alloc_bheap(compare_graph_int, g);
  for (i=0;i<size;i++) {
    associate_vertex_graph(g, i, (pointer_t)0);
    heap = put_bheap(heap, i);
  }
  for (i=size-1;i>=0;i--) {
    if (i == size-1) {
      elim[i] = seed;
      remove_bheap(heap, seed);
    } else
      elim[i] = extract_bheap(heap);
    processed_vertices = put_set(processed_vertices, elim[i]);
    neighbors = subtract_set(out_edges_graph(g, elim[i]), processed_vertices);
    size_neighbors = size_set(neighbors);
    for (j=0;j<size_neighbors;j++) {
      remove_bheap(heap, neighbors[j]);
      work = (int)mapsto_vertex_graph(g, neighbors[j]);
      work++;
      associate_vertex_graph(g, neighbors[j], (pointer_t)work);
      //      if (!contains_set(processed_vertices, neighbors[j]))
      heap = put_bheap(heap, neighbors[j]);
    }
    free_set(neighbors);
  }
  for (i=0;i<size;i++) {
    associate_vertex_graph(g, i, (pointer_t)NULL);
  }
  free_set(processed_vertices);
  free_bheap(heap);
}

void
mcs_graph_weight(graph_t g, int seed, int *elim, int** weights)
{

  /* weights is a two dimension array.
     weights[i] contains all the information about edge i. where i is the order placed into the graph. (not including self edges).
     weights[i][0] contains how many weights are in the array.
     weigths[i][1-weigths[i][0]] contain the weights.
  */

  int size = num_vertices_graph(g);
  int i,j,size_neighbors;
  bheap_t heap;
  set_t neighbors, processed_vertices;
  int work;
  processed_vertices = alloc_set(0);
  heap = alloc_bheap(compare_graph_int, g);
  for (i=0;i<size;i++) {
    associate_vertex_graph(g, i, (pointer_t)0);
    heap = put_bheap(heap, i);
  }
  for (i=size-1;i>=0;i--) {
    if (i == size-1) {
      elim[i] = seed;
      remove_bheap(heap, seed);
    } else
      elim[i] = extract_bheap(heap);
    processed_vertices = put_set(processed_vertices, elim[i]);
    neighbors = subtract_set(out_edges_graph(g, elim[i]), processed_vertices);
    size_neighbors = size_set(neighbors);
    for (j=0;j<size_neighbors;j++) {
      remove_bheap(heap, neighbors[j]);
      work = (int)mapsto_vertex_graph(g, neighbors[j]);
      work++;
      associate_vertex_graph(g, neighbors[j], (pointer_t)work);
      //      if (!contains_set(processed_vertices, neighbors[j]))
      heap = put_bheap(heap, neighbors[j]);
    }
    free_set(neighbors);
  }
  for (i=0;i<size;i++) {
    associate_vertex_graph(g, i, (pointer_t)NULL);
  }
  free_set(processed_vertices);
  free_bheap(heap);
}

















void
mcs_graph_layered_seeded(graph_t g, int seed, int *elim)
{
  int size = num_vertices_graph(g);
  int i,j,size_neighbors;
  bheap_t heap;
  set_t neighbors, processed_vertices;
  int work;
  processed_vertices = alloc_set(0);
  heap = alloc_bheap(compare_graph_int, g);
  for (i=0;i<size;i++) {
    heap = put_bheap(heap, i);
  }
  for (i=size-1;i>=0;i--) {
    if (i == size-1) {
      elim[i] = seed;
      remove_bheap(heap, seed);
    } else
      elim[i] = extract_bheap(heap);
    processed_vertices = put_set(processed_vertices, elim[i]);
    neighbors = subtract_set(out_edges_graph(g, elim[i]), processed_vertices);
    size_neighbors = size_set(neighbors);
    for (j=0;j<size_neighbors;j++) {
      remove_bheap(heap, neighbors[j]);
      work = (unsigned int)mapsto_vertex_graph(g, neighbors[j]);
      work++;
      associate_vertex_graph(g, neighbors[j], (pointer_t)work);
      //      if (!contains_set(processed_vertices, neighbors[j]))
      heap = put_bheap(heap, neighbors[j]);
    }
    free_set(neighbors);
  }
  free_set(processed_vertices);
  free_bheap(heap);
}

void mcs_graph_layered(graph_t g, int *elim)
{
  int size = num_vertices_graph(g);
  int i,w,e,pos;
  pos = -1;
  w = -1;
  e = 65536;
  for (i=0;i<size;i++) {
    if ((int)mapsto_vertex_graph(g, i)>w) {
      e = 65536;
      pos = i;
      continue;
    }
    if ((int)mapsto_vertex_graph(g, i)<w) 
      continue;
    if (size_set(out_edges_graph(g,i))<e) {
      e = size_set(out_edges_graph(g,i));
      pos = i;
      continue;
    }
  }
  mcs_graph_layered_seeded(g, pos, elim);
}

void mcs_graph_seed_int(graph_t g, set_t seed, int *elim, int dir)
{
  int size = num_vertices_graph(g);
  int size2;
  int i,j,size_neighbors;
  bheap_t heap;
  set_t neighbors, processed_vertices, inter;
  int work;
  processed_vertices = copy_set(seed);
  size2 = 0;
  heap = alloc_bheap(compare_graph_int, g);
  for (i=0;i<size;i++) {
    if (!contains_set(processed_vertices, i)) {
      inter = intersect_set(out_edges_graph(g, i), processed_vertices);
      associate_vertex_graph(g, i, (pointer_t)(size_set(inter)));
      heap = put_bheap(heap, i);
      free_set(inter);
      size2++;
    } else {
      associate_vertex_graph(g, i, (pointer_t)0);
    }
  }  
  for (i=(dir?0:size2-1);(dir?i<size2:i>=0);(dir?i++:i--)) {
    elim[i] = extract_bheap(heap);
    processed_vertices = put_set(processed_vertices, elim[i]);
    neighbors = subtract_set(out_edges_graph(g, elim[i]), processed_vertices);
    size_neighbors = size_set(neighbors);
    for (j=0;j<size_neighbors;j++) {
      remove_bheap(heap, neighbors[j]);
      work = (int)mapsto_vertex_graph(g, neighbors[j]);
      work++;
      associate_vertex_graph(g, neighbors[j], (pointer_t)work);
      //      if (!contains_set(processed_vertices, neighbors[j]))
      heap = put_bheap(heap, neighbors[j]);
    }
    free_set(neighbors);
  }
  for (i=0;i<size;i++) {
    associate_vertex_graph(g, i, (pointer_t)NULL);
  }
  free_set(processed_vertices);
  free_bheap(heap);
}

void mcs_graph_seed(graph_t g, set_t seed, int *elim)
{
  set_t v = vertex_set_graph(g);
  set_t other = subtract_set(v, seed);
  int so = size_set(other);
  mcs_graph_seed_int(g, seed, elim, 0);
  mcs_graph_seed_int(g, other, elim+so, 1);
  free_set(other);
}

int getNextChoice_graph(int c, int l)
{
  return (c+1)%l;
}

void sift_graph_width(graph_t g, int checks, int *elim)
{
  int mincost;
  int cost;
  int optpos;
  int choice = -1;
  int i;
  int temp;
  int len = num_vertices_graph(g);
  mincost = triangulate_graph(g, elim);
  while (checks > 0) {
    choice = getNextChoice_graph(choice, len);
    i = choice-1;
    optpos = choice;
    while (i>=0) {
      temp = elim[i];
      elim[i] = elim[i+1];
      elim[i+1] = temp;
      cost = triangulate_graph(g, elim);
      checks--;
      if (cost < mincost) {
	optpos = i;
	mincost = cost;
      }
      i--;
      if (cost > mincost*11/10)
	break;
    }
    i++;
    for (;i<choice;i++) {
      temp = elim[i];
      elim[i] = elim[i+1];
      elim[i+1] = temp;
    }
    i++;
    while (i<len) {
      temp = elim[i];
      elim[i] = elim[i-1];
      elim[i-1] = temp;
      cost = triangulate_graph(g, elim);
      checks--;
      if (cost < mincost) {
	optpos = i;
	mincost = cost;
      }
      i++;
      if (cost > mincost*11/10)
	break;
    }
    i--;
    for (;i>optpos;i--) {
      temp = elim[i];
      elim[i] = elim[i-1];
      elim[i-1] = temp;
    }
    printf("mincost=%d\n", mincost);
  }
}

void build_vo_graph(graph_t g, int options, int *elim)
{
  int i, width, minwidth, minwidthseed;
  int size = num_vertices_graph(g);
  minwidth = size+1;
  minwidthseed = 0;
  if (options & FASTSEED) {
    for (i=0;i<size;i++) {
      width = size_set(out_edges_graph(g, i));
      if (width < minwidth) {
	minwidth = width;
	minwidthseed = i;
      }
    }
  } else {
    for (i=0;i<size;i++) {
      if (options & LEXP)
	lexicographic_bfs_graph(g, i, elim);
      else if (options & LEXM)
	lexicographic_bfs_graph_min(g, i, elim);
      else
	mcs_graph(g, i, elim);
      width = triangulate_graph(g, elim);
      if (width < minwidth) {
	minwidth = width;
	minwidthseed = i;
      }      
    }
  }
  printf("w=%d\n", minwidth);
  if (options & LEXP)
    lexicographic_bfs_graph(g, minwidthseed, elim);
  else if (options & LEXM)
    lexicographic_bfs_graph_min(g, minwidthseed, elim);
  else
    mcs_graph(g, minwidthseed, elim);
}
















/********  percentage of variables free ***************************/
void
mcs_graph2(graph_t g, int* elim,int* freevariables, int numoffree)
{
  int size = num_vertices_graph(g);
  int i,j,size_neighbors;
  bheap_t heap;
  set_t neighbors, processed_vertices;
  int work;

  processed_vertices = alloc_set(0);
  heap = alloc_bheap(compare_graph_int, g);
  for (i=0;i<size;i++) {
    associate_vertex_graph(g, i, (pointer_t)0);
    heap = put_bheap(heap, i);
  }
  for (i=size-1;i>=0;i--) {
    if (i >= size-numoffree) {
      elim[i] = freevariables[size-1-i]-1;
      remove_bheap(heap, freevariables[size-1-i]-1);
    } else
      elim[i] = extract_bheap(heap);
    processed_vertices = put_set(processed_vertices, elim[i]);
    neighbors = subtract_set(out_edges_graph(g, elim[i]), processed_vertices);
    size_neighbors = size_set(neighbors);
    for (j=0;j<size_neighbors;j++) {
      remove_bheap(heap, neighbors[j]);
      work = (int)mapsto_vertex_graph(g, neighbors[j]);
      work++;
      associate_vertex_graph(g, neighbors[j], (pointer_t)work);
      //      if (!contains_set(processed_vertices, neighbors[j]))
      heap = put_bheap(heap, neighbors[j]);
    }
    free_set(neighbors);
  }
  for (i=0;i<size;i++) {
    associate_vertex_graph(g, i, (pointer_t)NULL);
  }
  free_bheap(heap);
}


void min_fill_graph2(graph_t g, int *elim,int* freevariables, int numoffree)
{
  int size = num_vertices_graph(g);
  int i,j,k,size_neighbors;
  bheap_t heap;
  set_t neighbors, processed_vertices, added_edges;
  set_t n2;
  int work;
  int oldsign = sign;
  sign = -1;
  processed_vertices = alloc_set(0);
  added_edges = alloc_set(0);
  heap = alloc_bheap(compare_graph_int, g);
  for (i=0;i<size;i++) {
    associate_vertex_graph(g, i, (pointer_t)get_fill_size(g, out_edges_graph(g, i)));
    heap = put_bheap(heap, i);
  }
  //  for (i=size-1;i>=0;i--) {
  //    if (i >= size-numoffree) {
  //      elim[i] = freevariables[size-1-i]-1;
  //      remove_bheap(heap, freevariables[size-1-i]-1);
  //    } else


  for (i=0;i<size;i++) {
    if (i<numoffree)
      {
	elim[i]=freevariables[i]-1;
	remove_bheap(heap,freevariables[i]-1);
      }
    else
      elim[i] = extract_bheap(heap);
    processed_vertices = put_set(processed_vertices, elim[i]);
    neighbors = subtract_set(out_edges_graph(g, elim[i]), processed_vertices);
    size_neighbors = size_set(neighbors);
    for (j=0;j<size_neighbors;j++) {
      for (k=j+1;k<size_neighbors;k++) {
	if (!has_edge_graph(g, neighbors[j], neighbors[k])) {
	  connect_graph(g, neighbors[j], neighbors[k]);
	  added_edges = put_set(added_edges, neighbors[j]*size+neighbors[k]);
	}
      }
    }
    for (j=0;j<size_neighbors;j++) {
      remove_bheap(heap, neighbors[j]);
      n2 = subtract_set(out_edges_graph(g, neighbors[j]), processed_vertices);
      work = get_fill_size(g, n2);
      associate_vertex_graph(g, neighbors[j], (pointer_t)work);
      heap = put_bheap(heap, neighbors[j]);
    }
    free_set(neighbors);
  }
  for (i=0;i<size;i++) {
    associate_vertex_graph(g, i, (pointer_t)NULL);
  }
  size_neighbors = size_set(added_edges);
  for (i=0;i<size_neighbors;i++) {
    j = added_edges[i]/size;
    k = added_edges[i]-j*size;
    disconnect_graph(g, j, k);
  }
  free_set(added_edges);    
  free_set(processed_vertices);
  free_bheap(heap);
  sign = oldsign;
}


void min_induced_width_graph2(graph_t g, int *elim,int* freevariables, int numoffree)
{
  int size = num_vertices_graph(g);
  int i,j,k,size_neighbors;
  bheap_t heap;
  set_t neighbors, processed_vertices, added_edges;
  int work;
  int *neighbor_edges;
  int oldsign = sign;
  sign = -1;
  processed_vertices = alloc_set(0);
  added_edges = alloc_set(0);
  heap = alloc_bheap(compare_graph_int, g);
  for (i=0;i<size;i++) {
    associate_vertex_graph(g, i, (pointer_t)(size_set(out_edges_graph(g, i))));
    heap = put_bheap(heap, i);
  }
  neighbor_edges = (int *)alloca(sizeof(int)*size);
  for (i=0;i<size;i++) {
    if (i<numoffree)
      {
	elim[i]=freevariables[i]-1;
	remove_bheap(heap,freevariables[i]-1);
      }
    else
      elim[i] = extract_bheap(heap);
    processed_vertices = put_set(processed_vertices, elim[i]);
    neighbors = subtract_set(out_edges_graph(g, elim[i]), processed_vertices);
    size_neighbors = size_set(neighbors);
    for (j=0;j<size_neighbors;j++)
      neighbor_edges[j] = -1;
    for (j=0;j<size_neighbors;j++) {
      for (k=j+1;k<size_neighbors;k++) {
	if (!has_edge_graph(g, neighbors[j], neighbors[k])) {
	  connect_graph(g, neighbors[j], neighbors[k]);
	  added_edges = put_set(added_edges, neighbors[j]*size+neighbors[k]);
	  neighbor_edges[j]++;
	  neighbor_edges[k]++;
	}
      }
    }
    for (j=0;j<size_neighbors;j++) {
      remove_bheap(heap, neighbors[j]);
      work = (int)mapsto_vertex_graph(g, neighbors[j]);
      work += neighbor_edges[j];
      associate_vertex_graph(g, neighbors[j], (pointer_t)work);
      heap = put_bheap(heap, neighbors[j]);
    }
    free_set(neighbors);
  }
  for (i=0;i<size;i++) {
    associate_vertex_graph(g, i, (pointer_t)NULL);
  }
  size_neighbors = size_set(added_edges);
  for (i=0;i<size_neighbors;i++) {
    j = added_edges[i]/size;
    k = added_edges[i]-j*size;
    disconnect_graph(g, j, k);
  }
  free_set(added_edges);    
  free_set(processed_vertices);
  free_bheap(heap);
  sign = oldsign;
}

void
lexicographic_bfs_graph_min2(graph_t g, int *elim,int* freevariables, int numoffree)
{
  int size = num_vertices_graph(g);
  int i,j,size_neighbors;
  bheap_t heap;
  set_t neighbors, processed_vertices;
  lex_t work;
  processed_vertices = alloc_set(0);
  for (i=0;i<size;i++) {
    work = alloc_lexset();
    associate_vertex_graph(g, i, (pointer_t)work);
  }
  heap = alloc_bheap(compare_graph_lexset, g);
  for (i=0;i<size;i++) {
    //    if (i != seed)
      heap = put_bheap(heap, i);
  }
  for (i=size-1;i>=0;i--) {
    if (i >= size-numoffree) {
      elim[i] = freevariables[size-1-i]-1;
      remove_bheap(heap, freevariables[size-1-i]-1);
    } else
      elim[i] = extract_bheap(heap);
    processed_vertices = put_set(processed_vertices, elim[i]);
    neighbors = subtract_set(out_edges_graph(g, elim[i]), processed_vertices);
    size_neighbors = size_set(neighbors);
    for (j=0;j<size_neighbors;j++) {
      remove_bheap(heap, neighbors[j]);
      work = mapsto_vertex_graph(g, neighbors[j]);
      add_lexset(work, i);
      if (!contains_set(processed_vertices, neighbors[j]))
	heap = put_bheap(heap, neighbors[j]);
    }
    neighbors = subtract_set(vertex_set_graph(g), processed_vertices);
    size_neighbors = size_set(neighbors);
    for (j=0;j<size_neighbors;j++) {
      work = mapsto_vertex_graph(g, neighbors[j]);
      if (contains_lexset(work, elim[i])) continue;
      if (graph_backward_is_reachable(g, neighbors[j], elim[i], graph_lexset_lessthen, (pointer_t)work)) {
	remove_bheap(heap, neighbors[j]);
	add_lexset(work, i);
	if (!contains_set(processed_vertices, neighbors[j]))
	  heap = put_bheap(heap, neighbors[j]);
      }
    }
  }
  for (i=0;i<size;i++) {
    work = mapsto_vertex_graph(g, i);
    free_lexset(work);
    associate_vertex_graph(g, i, (pointer_t)NULL);
  }
  free_bheap(heap);
  free_set(processed_vertices);
}


void
lexicographic_bfs_graph2(graph_t g, int *elim,int* freevariables, int numoffree)
{
  int size = num_vertices_graph(g);
  int i,j,size_neighbors;
  bheap_t heap;
  set_t neighbors, processed_vertices;
  lex_t work;
  processed_vertices = alloc_set(0);
  for (i=0;i<size;i++) {
    work = alloc_lexset();
    associate_vertex_graph(g, i, (pointer_t)work);
  }
  heap = alloc_bheap(compare_graph_lexset, g);
  for (i=0;i<size;i++) {
    //    if (i != seed)
      heap = put_bheap(heap, i);
  }
  for (i=size-1;i>=0;i--) {
    if (i >= size-numoffree) {
      elim[i] = freevariables[size-1-i]-1;
      remove_bheap(heap, freevariables[size-1-i]-1);
    } else
      elim[i] = extract_bheap(heap);
    processed_vertices = put_set(processed_vertices, elim[i]);
    neighbors = subtract_set(out_edges_graph(g, elim[i]), processed_vertices);
    size_neighbors = size_set(neighbors);
    for (j=0;j<size_neighbors;j++) {
      remove_bheap(heap, neighbors[j]);
      work = mapsto_vertex_graph(g, neighbors[j]);
      add_lexset(work, i);
      if (!contains_set(processed_vertices, neighbors[j]))
	heap = put_bheap(heap, neighbors[j]);
    }
  }
  for (i=0;i<size;i++) {
    work = mapsto_vertex_graph(g, i);
    free_lexset(work);
    associate_vertex_graph(g, i, (pointer_t)NULL);
  }
  free_bheap(heap);
  free_set(processed_vertices);
}
