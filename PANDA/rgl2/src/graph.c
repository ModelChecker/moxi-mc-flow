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

typedef struct
{
  int num_edges;

  word_t properties;

  set_t front_edges;
  set_t back_edges;
  
  set_t vertices;
} g_t;

/**
 * Gets the properties tag.
 */

word_t get_properties_graph(graph_t g)
{
  g_t *gr = (g_t *) g;

  return gr->properties;
}

/**
 * Allocates a graph object.
 *
 * @param properties a union of graph property masks.
 */

graph_t 
alloc_graph(word_t properties)
{
  g_t *g = (g_t *) malloc(sizeof(g_t));

  g->num_edges = 0;
  g->properties = properties;
  
  g->front_edges = alloc_set(SP_MAP);
  
  if ((GP_DIRECTED | GP_BACK_EDGES) & properties) 
    g->back_edges = alloc_set(SP_MAP);
  else g->back_edges = 0;

  if (GP_VERTEX_SET & properties) {
    if (GP_VERTEX_MAP & properties) 
      g->vertices = alloc_set(SP_MAP);          
    else 
      g->vertices = alloc_set(0);
  }
  else g->vertices = 0;

  return (graph_t) g;
}

/**
 * Deallocates the graph.
 */

void 
free_graph(graph_t g)
{
  g_t *gr = (g_t *) g;

  pointer_t *mt;
  int i;

  int n = size_set(gr->front_edges);

  mt = maptable_set(gr->front_edges);
  
  for (i=0; i<n; i++) {
    if (mt[i]) {
      set_t s = (set_t) mt[i];

      free_set(s);
    }
  }

  free_set(gr->front_edges);

  if (gr->back_edges) {
    mt = maptable_set(gr->back_edges);
    n = size_set(gr->back_edges);
    
    for (i=0; i<n; i++) {
      if (mt[i]) {
	set_t s = (set_t) mt[i];
	
	free_set(s);	
      }
    }

    free_set(gr->back_edges);
  }

  if (gr->vertices) free_set(gr->vertices);

  free(gr);
}

/**
 * Returns the number of vertices stored in the graph.
 */

int 
num_vertices_graph(graph_t g)
{
  g_t *gr = (g_t *) g;

  if (gr->properties & GP_VERTEX_SET) 
    return size_set(gr->vertices);
  else return size_set(gr->front_edges);
}

/**
 * Returns the number of edges stored in the graph.
 */

int 
num_edges_graph(graph_t g)
{
  g_t *gr = (g_t *) g;

  assert (gr->properties & GP_EDGE_NUMBER);

  return gr->num_edges;
}

/**
 * Connects two vertices.
 *
 * @param g a graph.
 * @param idA the 'from' vertex id.
 * @param idB the 'to' vertex id.
 */

void 
connect_graph(graph_t g, int idA, int idB)
{
  g_t *gr = (g_t *) g;

  set_t edges = (set_t) mapsto_set(gr->front_edges, idA);

  //  fprintf(stderr, "%i %i\n", idA, idB);

  if (edges == NIL) {
    if (gr->properties & GP_EDGE_MAP) 
      edges = alloc_set(SP_MAP);
    else 
      edges = alloc_set(SP_MAP);
  }

  if (gr->properties & GP_EDGE_NUMBER) 
    if (contains_set(edges, idB) == FALSE) gr->num_edges ++;
  
  edges = put_set(edges, idB);

  gr->front_edges = associate_set(gr->front_edges, idA, edges);

  if ((gr->properties & GP_DIRECTED) == 0) {
    edges = (set_t) mapsto_set(gr->front_edges, idB);

    if (edges == NIL) {
      if (gr->properties & GP_EDGE_MAP) 
	edges = alloc_set(SP_MAP);
      else 
	edges = alloc_set(SP_MAP);
    } 
    
    edges = put_set(edges, idA);

    gr->front_edges = associate_set(gr->front_edges, idB, edges);
  }
  else if (gr->properties & GP_BACK_EDGES) {
    edges = (set_t) mapsto_set(gr->back_edges, idB);

    if (edges == NIL) {
      if (gr->properties & GP_EDGE_MAP) 
	edges = alloc_set(SP_MAP);
      else 
	edges = alloc_set(SP_MAP);
    } 
    
    edges = put_set(edges, idA);

    gr->back_edges = associate_set(gr->back_edges, idB, edges);
  }

  if (gr->properties & GP_VERTEX_SET) {
    gr->vertices = put_set(gr->vertices, idA);
    gr->vertices = put_set(gr->vertices, idB);
  }
}

/**
 * Disconnects two vertices.
 *
 * @param g a graph.
 *
 * @param idA the 'from' vertex id.
 * @param idB the 'to' vertex id.
 *
 * @return TRUE if an edge was deleted and FALSE otherwise.
 */

boolean_t 
disconnect_graph(graph_t g, int idA, int idB)
{
  g_t *gr = (g_t *) g;

  set_t edges = (set_t) mapsto_set(gr->front_edges, idA);
  boolean_t result;

  if (edges == NIL) return FALSE;

  result = remove_set(edges, idB);

  if ((gr->properties & GP_DIRECTED) == 0) {
    edges = (set_t) mapsto_set(gr->front_edges, idB);

    remove_set(edges, idA);
  }
  else if (gr->properties & GP_BACK_EDGES) {
    edges = (set_t) mapsto_set(gr->back_edges, idB);

    remove_set(edges, idA);
  }  

  if (gr->properties & GP_EDGE_NUMBER && result) gr->num_edges --;
  
  return result;
}

/**
 * Checks existence of an edge.
 *
 * @param g a graph.
 *
 * @param idA the 'from' vertex id.
 * @param idB the 'to' vertex id.
 *
 * @return TRUE if the edge existed and FALSE otherwise.
 */

boolean_t
has_edge_graph(graph_t g, int idA, int idB)
{
  g_t *gr = (g_t *) g;

  set_t edges = (set_t) mapsto_set(gr->front_edges, idA); 

  if (edges == NIL) return FALSE;

  return contains_set(edges, idB);
}

/**
 * Returns a set of vertices that have edges going to a given vertex.
 * This will fail on a directed graph if GP_BACK_EDGES is not set.
 *
 * @param g a graph.
 *
 * @param id a vertex id.
 *
 * @return the set of incoming edges to vertex 'id'.
 */

set_t 
in_edges_graph(graph_t g, int id)
{
  g_t *gr = (g_t *) g;

  if (gr->properties & GP_DIRECTED) {
    assert (gr->properties & GP_BACK_EDGES);

    return (set_t) mapsto_set(gr->back_edges, id);
  }
  else 
    return (set_t) mapsto_set(gr->front_edges, id);
}

/**
 * Returns a set of vertices that have edges coming from a given vertex.
 *
 * @param g a graph.
 *
 * @param id a vertex id.
 *
 * @return the set of outgoing edges to vertex 'id'.
 */

set_t 
out_edges_graph(graph_t g, int id)
{
  g_t *gr = (g_t *) g;

  return (set_t) mapsto_set(gr->front_edges, id);
}

/**
 * Returns the vertex set for the graph.  Requires GP_VERTEX_SET to be set.
 * It is not correct to modify the set.
 *
 * @param g a graph.
 *
 * @return the set of vertices in the graph.
 */

set_t 
vertex_set_graph(graph_t g)
{
  g_t *gr = (g_t *) g;

  assert (gr->properties & GP_VERTEX_SET);

  return gr->vertices;
}

/**
 * Checks to see if a vertex is in the graph.
 *
 * @param g a graph.
 * 
 * @param id a vertex id.
 *
 * @return TRUE if a vertex existed and FALSE otherwise.
 */

boolean_t 
contains_vertex_graph(graph_t g, int id)
{
  g_t *gr = (g_t *) g;

  if (gr->properties & GP_VERTEX_SET) return contains_set(gr->vertices, id);
  else if (gr->properties & GP_BACK_EDGES) 
    return contains_set(gr->front_edges, id) && contains_set(gr->back_edges, id);
  else return contains_set(gr->front_edges, id);
}

/**
 * Associates a vertex with an object.  Requires GP_VERTEX_MAP to be set.
 *
 * @param g a graph.
 *
 * @param id a vertex id.
 * @param obj the object to be associated with vertex 'id'.
 */

void 
associate_vertex_graph(graph_t g, int id, pointer_t obj)
{
  g_t *gr = (g_t *) g;
  
  assert (gr->properties & GP_VERTEX_SET && gr->properties & GP_VERTEX_MAP);
  
  gr->vertices = associate_set(gr->vertices, id, obj);
}

/**
 * Returns the object associated with vertex 'id'.  Requires GP_VERTEX_MAP to be set.
 *
 * @param g a graph.
 *
 * @param id a vertex id.
 *
 * @return the object associated with vertex 'id' or NIL if not availible.
 */

pointer_t 
mapsto_vertex_graph(graph_t g, int id)
{
  g_t *gr = (g_t *) g;
  
  assert (gr->properties & GP_VERTEX_SET && gr->properties & GP_VERTEX_MAP);

  return mapsto_set(gr->vertices, id);
}


/**
 * Associates an edge with an object.  Requires GP_EDGE_MAP to be set.
 *
 * @param g a graph.
 *
 * @param idA the 'from' vertex.
 * @param idB the 'to' vertex.
 *
 * @param obj the object to be associated with edge (idA, idB).
 */

void 
associate_edge_graph(graph_t g, int idA, int idB, pointer_t obj)
{
  g_t *gr = (g_t *) g;
  set_t edges;
  
  assert (gr->properties & GP_EDGE_MAP);
  
  connect_graph(g, idA, idB);
  
  edges = (set_t) mapsto_set(gr->front_edges, idA);   

  assert(edges);

  associate_set(edges, idB, obj);  

  if ((gr->properties & GP_DIRECTED) == 0) {
    edges = (set_t) mapsto_set(gr->front_edges, idB);
    
    assert (edges);

    associate_set(edges, idA, obj);
  }
}

/**
 * Returns the object associated with an edge.  Requires GP_EDGE_MAP to be set.
 *
 * @param g a graph.
 *
 * @param idA the 'from' vertex.
 * @param idB the 'to' vertex.
 *
 * @return the object associated with (idA, idB) or NIL if not availible.
 */

pointer_t 
mapsto_edge_graph(graph_t g, int idA, int idB)
{
  g_t *gr = (g_t *) g;
  set_t edges = (set_t) mapsto_set(gr->front_edges, idA);   

  if (edges == NIL) return NIL;

  return mapsto_set(edges, idB);
}

/** 
 * Removes a vertex from the graph, removing its edges.
 *
 * @param g a graph.
 * @param id the vertex to remove.
 *
 * @return TRUE if a vertex was removed, FALSE otherwise.
 */

boolean_t 
remove_vertex_graph(graph_t g, int id)
{
  g_t *gr = (g_t *) g;
  set_t edges = (set_t) mapsto_set(gr->front_edges, id);   
  int i;
  int n = size_set(edges);

  for (i=0; i<n; i++) disconnect_graph(g, id, edges[i]);

  free_set(edges);

  remove_set(gr->front_edges, id);

  if ((gr->properties & GP_DIRECTED) && (gr->properties & GP_BACK_EDGES)) {
    edges = (set_t) mapsto_set(gr->back_edges, id);   
    n = size_set(edges);

    for (i=0; i<n; i++) disconnect_graph(g, edges[i], id);

    free_set(edges);
    
    remove_set(gr->back_edges, id);
  }

  if (gr->properties & GP_VERTEX_SET) 
    return remove_set(gr->vertices, id);
  
  return TRUE;  
}


/**
 * Destroys all memory associated with a graph.  This is dangerous.
 *
 * @param g a graph.
 */

void 
purge_graph(graph_t g)
{
  g_t *gr = (g_t *) g;

  if ((gr->properties & GP_EDGE_MAP)) {
    set_t *e_sets = (set_t *) maptable_set(gr->front_edges);
    int n = size_set(gr->front_edges);
    int i;
    
    for (i=0; i<n; i++) {
      if (e_sets[i]) {
	pointer_t *datas = maptable_set(e_sets[i]);
	int m = size_set(e_sets[i]);
	int j;
	
	for (j=0; j<m; j++)
	  if (datas[j]) free(datas[j]);       
      }
    }
  }

  if ((gr->properties & GP_VERTEX_MAP)) {
    pointer_t *datas = maptable_set(gr->vertices);
    int n = size_set(gr->vertices);
    int i;
    
    for (i=0; i<n; i++)
      if (datas[i]) free(datas[i]);
  }

  free_graph(g);
}

/**
 * Pretty print the graph.
 *
 * @param fp a file pointer.
 * @param g a graph.
 */

void 
pretty_print_graph(FILE *fp, graph_t g)
{
    g_t *gr = (g_t *) g;
    int i, j;
    int n, m;
    set_t edges;
    
    fprintf(fp, "num_edges: %i properties: %x\n", gr->num_edges, gr->properties);
    
    n = size_set(gr->front_edges);
    
    //pretty_print_set(stdout, gr->front_edges);
    
    for (i=0; i<n; i++)
    {
	edges = (set_t) ith_map_set(gr->front_edges, i);
	
	fprintf(fp, "%i: ", gr->front_edges[i]);
	
	if (edges != NIL)
	{
	    m = size_set(edges);
	    
	    for (j=0; j<m; j++) 
		fprintf(fp, "%i ", edges[j]);      
	}
	
	fprintf(fp, "\n");
    }
}
