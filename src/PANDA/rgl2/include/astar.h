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


#ifndef __RGL_ASTAR_H__
#define __RGL_ASTAR_H__

#include "graph.h"

BEGIN_C_DECL

typedef double (*cost_fn_t)(pointer_t, int, int);
typedef double (*estimate_fn_t)(pointer_t, int);

/**
 * Computes a path between two vertices in a graph using the A-star heuristic.
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

double get_shortest_path_astar(graph_t graph, int start, int finish, 
			       cost_fn_t cost_fn, estimate_fn_t estimate_fn,
			       pointer_t cost_data, pointer_t estimate_data,
			       int *len, int **path);

END_C_DECL

#endif
