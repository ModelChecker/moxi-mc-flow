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


#include "kpartition.h"

#include <math.h>

set_t 
random_k_partition(graph_t g, int k)
{
  set_t vertices = vertex_set_graph(g);
  set_t partition = alloc_set(SP_MAP);

  int n = size_set(vertices);
  int i;
  
  for (i=0; i<n; i++) {
    int z = i % k;
    
    partition = associate_set(partition, vertices[i], (pointer_t) z);
  }

  return partition;
}

int 
evaluate_k_partition(graph_t g, set_t partition)
{
  int i;
  int conflicts = 0;

  int n = size_set(partition);

  for (i=0; i<n; i++) {
    int v = partition[i];
    set_t edges = out_edges_graph(g, v);
    int m = size_set(edges);
    int j;

    pointer_t rep = mapsto_set(partition, v);
    
    for (j=0; j<m; j++) {
      pointer_t trep = mapsto_set(partition, edges[j]);
      if (rep != trep) conflicts++;
    }
  }

  return conflicts / 2;
}

double
communications_k_partition(graph_t g, set_t partition, int k)
{
  int i;
  int n = size_set(partition);
  int comm = 0;
  
  for (i=0; i<n; i++) {
    set_t trash = alloc_set(0);
    set_t edges = out_edges_graph(g, partition[i]);
    int m = size_set(edges);
    int j;

    for (j=0; j<m; j++) {
      int rep = (int) mapsto_set(partition, edges[j]);
      
      trash = put_set(trash, rep);
    }

    comm += size_set(trash);

    free_set(trash);
  }
  
  return (double) comm / (double) n;
}

static
double calc_projection(double *pta, double *ptb, double *pt, int dim)
{
  double dp = 0.0;
  double n = 0.0;
  int i;
  
  for (i=0; i<dim; i++) {
    dp += (ptb[i] - pta[i]) * (pt[i] - pta[i]);
    n += (ptb[i] - pta[i]) * (ptb[i] - pta[i]);
  }

  return dp / n;
}

static double *tval;

static int cmp_tval(const void *a, const void *b)
{
  int av = *((int *) a);
  int bv = *((int *) b);

  if (tval[av] < tval[bv]) return -1;
  else if (tval[av] == tval[bv]) return 0;
  else return 1;
}

set_t 
line_projection_partition(set_t pts, int dim, int k)
{
  int n = size_set(pts);
  int a = random() % n;
  int b = random() % n;
  double *pta, *ptb;
  int *ids;
  int psize = n / k;
  int prem = n % k;

  int i, j, count;

  set_t partition = alloc_set(SP_MAP);

  while (a == b) b = random() % n;

  pta = (double *) mapsto_set(pts, a);
  ptb = (double *) mapsto_set(pts, b);

  tval = (double *) malloc(sizeof(double) * n);
  ids = (int *) malloc(sizeof(int) * n);
  
  for (i=0; i<n; i++) {
    tval[i] = calc_projection(pta, ptb, (double *) ith_map_set(pts, i), dim);
    ids[i] = pts[i];
  }
  
  qsort(ids, n, sizeof(int), cmp_tval);

  free(tval);

  count = 0;
  for (i=0; i<k; i++) {
    int m = psize;
    if (i < prem) m = m + 1;
    
    for (j=0; j<m; j++) 
      partition = associate_set(partition, ids[count++], (pointer_t) i);    
  }

  free(ids);

  return partition;
}

set_t 
iterative_k_partition(graph_t g, int *centers, int k)
{
  set_t *frontiers = malloc(sizeof(set_t) * k);  // the immediate edge neighbourhood around edge partition set
                                                 // frontiers[i] is the ith neighbourhood
                                                 // a vertex can be in the frontier if it hasn't been assigned yet
                                                 // the set map stores the number of edges from each vertex to 
                                                 // the partition

  set_t partition = alloc_set(SP_MAP);           // partition set - maps to the colour each vertex got with -1 being
                                                 // unassigned
  set_t vertices = vertex_set_graph(g);
  
  int n = size_set(vertices);

  int i; 
  int count = 0;   // total number of processed vertices.

  for (i=0; i<k; i++) 
    frontiers[i] = alloc_set(SP_MAP);
  
  for (i=0; i<n; i++)
    partition = associate_set(partition, vertices[i], (pointer_t) -1);  // all vertices unassigned
  
  for (i=0; i<k; i++) 
    frontiers[i] = associate_set(frontiers[i], centers[i], (pointer_t) 0);  // seed the frontiers with the centers
  

  i = 0;
  while (count < n) {  // until all vertices partitioned
    int j;
    int m = size_set(frontiers[i]);   // how many frontier vertices?
    int mx = -1;
    int mv = -1;

    for (j=0; j<m; j++) {         // find the vertex with largest number of incident edges to the partition
      int v = (int) ith_map_set(frontiers[i], j);   

      if (v > mv) {
	mx = j;
	mv = v;
      }
    }

    {
      int choice;
      set_t edges;
      int m;
      
      if (mx >= 0) choice = frontiers[i][mx];   // if a good vertex was found - choose it
      else {
	do {
	  choice = vertices[random() % n];
	} while((int) mapsto_set(partition, choice) != -1);  // otherwise choose one at random
      }
      
      edges = out_edges_graph(g, choice);   // get the edges from the chosen vertex
      m = size_set(edges);

      partition = associate_set(partition, choice, (pointer_t) i);  // assign it to the ith partition

      for (j=0; j<m; j++) {
	if ((int) mapsto_set(partition, edges[j]) == -1) {  // if the out vertex is unassigned
	  int v = (int) mapsto_set(frontiers[i], edges[j]);

	  frontiers[i] = associate_set(frontiers[i], edges[j], (pointer_t) (v + 1));  // add it to the frontier
                                                                                      // increment its valence
	}
      }

      for (j=0; j<k; j++) 
	remove_set(frontiers[j], choice);   // remove the chosen vertex from all frontiers

      count++;   // one vertex down.
    }
   
    i = (i+1) % k;   // next partition
  }

  for (i=0; i<k; i++) free_set(frontiers[i]);
  free(frontiers);

  return partition;
}

int *
random_centers(graph_t g, int k)
{
  set_t vertices = vertex_set_graph(g);
  int n = size_set(vertices);
  int i;

  int *centers = (int *) malloc(sizeof(int) * k);

  for (i=0; i<k; i++) {
    int j;
    do {
      centers[i] = vertices[random() % n];
      for (j=0; j<i; j++)
	if (centers[j] == centers[i]) break;
    } while (j < i);
  }
  
  return centers;
}

static
double d_squared(double *pta, double *ptb, int dim)
{
  double d = 0.0;
  int i;

  for (i=0; i<dim; i++) 
    d += (ptb[i] - pta[i]) * (ptb[i] - pta[i]);

  return d;
}

int *
k_median_approx(set_t pts, int k, int dim)
{
  int n = size_set(pts);

  int *centers = (int *) malloc(sizeof(int) * k);
  double *distances = (double *) malloc(n * sizeof(double));
  int i;
  double *pt;
  int start = random() % n;
  
  centers[0] = pts[start];

  pt = (double *) mapsto_set(pts, centers[0]);

  for (i=0; i<n; i++) {
    double *ptb = (double *) ith_map_set(pts, i);
    distances[i] = d_squared(pt, ptb, dim);
  }
  
  for (i=1; i<k; i++) {
    int mx = -1;
    double md = -1.0;
    int j;
    
    for (j=0; j<n; j++) {
      if (distances[j] > md) {
	mx = j;
	md = distances[j];
      }
    }

    centers[i] = pts[mx];
    pt = (double *) mapsto_set(pts, centers[i]);

    for (j=0; j<n; j++) {      
      double *ptb = (double *) ith_map_set(pts, j);
      double d = d_squared(pt, ptb, dim);

      if (d < distances[j]) distances[j] = d;      
    }
  }
  
  free(distances);
  
  return centers;
}
