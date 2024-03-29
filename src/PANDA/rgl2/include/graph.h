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


#ifndef _____RGL_GRAPH___H___
#define _____RGL_GRAPH___H___

#include "defs.h"
#include "set.h"

BEGIN_C_DECL

/**
 * A graph type.
 */

typedef pointer_t graph_t;

/**
 * An enumeration of graph properties.
 */

typedef enum 
  {
    GP_DIRECTED = 0x01,      /* marks the graph as directed */
    GP_VERTEX_SET = 0x02,    /* adds a vertex set */
    GP_VERTEX_MAP = 0x04,    /* adds a vertex map */
    GP_EDGE_MAP = 0x08,      /* adds an edge map */
    GP_BACK_EDGES = 0x10,    /* stores back edges for a directed graph */
    GP_EDGE_NUMBER = 0x20    /* stores edge count for any graph */
  } graph_properties_t;


/**
 * Gets the properties tag.
 */

word_t get_properties_graph(graph_t g);

/**
 * Allocates a graph object.
 *
 * @param properties a union of graph property masks.
 */

graph_t alloc_graph(word_t properties);

/**
 * Deallocates the graph.
 */

void free_graph(graph_t g);

/**
 * Returns the number of vertices stored in the graph.
 */

int num_vertices_graph(graph_t g);

/**
 * Returns the number of edges stored in the graph.
 */

int num_edges_graph(graph_t g);

/**
 * Connects two vertices.
 *
 * @param g a graph.
 * @param idA the 'from' vertex id.
 * @param idB the 'to' vertex id.
 */

void connect_graph(graph_t g, int idA, int idB);

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

boolean_t disconnect_graph(graph_t g, int idA, int idB);

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

boolean_t has_edge_graph(graph_t g, int idA, int idB);

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

set_t in_edges_graph(graph_t g, int id);

/**
 * Returns a set of vertices that have edges coming from a given vertex.
 *
 * @param g a graph.
 *
 * @param id a vertex id.
 *
 * @return the set of outgoing edges to vertex 'id'.
 */

set_t out_edges_graph(graph_t g, int id);

/**
 * Returns the vertex set for the graph.  Requires GP_VERTEX_SET to be set.
 * It is not correct to modify the set.
 *
 * @param g a graph.
 *
 * @return the set of vertices in the graph.
 */

set_t vertex_set_graph(graph_t g);

/**
 * Checks to see if a vertex is in the graph.
 *
 * @param g a graph.
 * 
 * @param id a vertex id.
 *
 * @return TRUE if a vertex existed and FALSE otherwise.
 */

boolean_t contains_vertex_graph(graph_t g, int id);

/**
 * Associates a vertex with an object.  Requires GP_VERTEX_MAP to be set.
 *
 * @param g a graph.
 *
 * @param id a vertex id.
 * @param obj the object to be associated with vertex 'id'.
 */

void associate_vertex_graph(graph_t g, int id, pointer_t obj);

/**
 * Returns the object associated with vertex 'id'.  Requires GP_VERTEX_MAP to be set.
 *
 * @param g a graph.
 *
 * @param id a vertex id.
 *
 * @return the object associated with vertex 'id' or NIL if not availible.
 */

pointer_t mapsto_vertex_graph(graph_t g, int id);

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

void associate_edge_graph(graph_t g, int idA, int idB, pointer_t obj);

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

pointer_t mapsto_edge_graph(graph_t g, int idA, int idB);

/** 
 * Removes a vertex from the graph, removing its edges.
 *
 * @param g a graph.
 * @param id the vertex to remove.
 *
 * @return TRUE if a vertex was removed, FALSE otherwise.
 */

boolean_t remove_vertex_graph(graph_t g, int id);

/**
 * Destroys all memory associated with a graph.  This is dangerous.
 *
 * @param g a graph.
 */

void purge_graph(graph_t g);

/**
 * Pretty print the graph.
 *
 * @param fp a file pointer.
 * @param g a graph.
 */

void pretty_print_graph(FILE *fp, graph_t g);

END_C_DECL

#endif
