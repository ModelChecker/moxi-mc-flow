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
#include "random.h"
#include "knn.h"
#include "graphalg.h"

double **uniform_data(int n, int dim)
{
  double **pts = (double **) malloc(sizeof(double *) * n);
  int i, j;

  for (i=0; i<n; i++) {
    pts[i] = (double *) malloc(sizeof(double) * dim);

    for (j=0; j<dim; j++)
      pts[i][j] = uniform();
  }

  return pts;
}

graph_t 
knn_graph(double **pts, int n, int dim, int k)
{
  kdtree_t *tree;
  int *id = (int *) malloc(sizeof(int) * n);
  int i;
  graph_t g = alloc_graph(GP_VERTEX_SET | GP_EDGE_NUMBER);

  for (i=0; i<n; i++) id[i] = i;

  tree = construct_kdtree(dim, 20, n, id, pts);

  for (i=0; i<n; i++) {
    set_t neigh = closest_k_neighbours(tree, k + 1, pts[i]);
    int m = size_set(neigh);
    int j;

    for (j=0; j<m; j++) {
      if (neigh[j] == i) continue;
      connect_graph(g, i, neigh[j]);
    }

    free_set(neigh);
  }

  free(id);
  free_kdtree(tree);

  return g;
}

int logceil2(int x) {
  int v = 0;
  if (x < 1) return -1;

  while (x > 1) {
    x /= 2;
    v++;
  }

  return v;
}

int main(int argc, char **argv)
{
  int n = 10000;
  int dim = 3;
  int k = 10;
  int p = 32;

  double **pts;
  graph_t g;
  set_t partition;

  set_t pset = alloc_set(SP_MAP);
  int *centers;
  int i;

  generate_seed();

  if (argc > 1) {
    n = atoi(argv[1]);
    k = 2 * logceil2(n);
    p = 4 * logceil2(n);
  }
  if (argc > 2) {
    k = atoi(argv[2]);
  }

  pts = uniform_data(n, dim);
  g = knn_graph(pts, n, dim, k);

  for (i=0; i<n; i++) pset = associate_set(pset, i, pts[i]);

  //printf("connected components: %i\n", num_connected_components(g));

  //printf("number of edges: %i\n", num_edges_graph(g));
  
  printf("%i %i %i %i ", n, k, p, num_edges_graph(g));

  partition = random_k_partition(g, p);
  
  //printf("random partition quality: %i\n", evaluate_k_partition(g, partition));
  
  //printf("%i ", evaluate_k_partition(g, partition));
  printf("%f ", communications_k_partition(g, partition, k));

  partition = line_projection_partition(pset, dim, p);

  //printf("%i ", evaluate_k_partition(g, partition));
  printf("%f ", communications_k_partition(g, partition, k));

  //printf("proj partition quality: %i\n", evaluate_k_partition(g, partition));
  
  centers = random_centers(g, k);
  partition = iterative_k_partition(g, centers, k);

  //printf("%i ", evaluate_k_partition(g, partition));
  printf("%f ", communications_k_partition(g, partition, k));

  //printf("iter partition quality: %i\n", evaluate_k_partition(g, partition));

  centers = k_median_approx(pset, k, dim);
  partition = iterative_k_partition(g, centers, k);

  //printf("%i ", evaluate_k_partition(g, partition));
  printf("%f ", communications_k_partition(g, partition, k));
  printf("\n");
  fflush(stdout);
  
  //printf("iter med partition quality: %i\n", evaluate_k_partition(g, partition));
  

  return 1;
}
