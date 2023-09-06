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


#include "knn.h"

typedef struct 
{
  int id;
  double *pt;
  double distance;
} c_t;

static inline 
void 
add_element(c_t *cs, int *n, int id, double *pt, double distance)
{
  int i;
  c_t temp;
  int m;
  
  cs[*n].id = id;
  cs[*n].pt = pt;
  cs[*n].distance = distance;

  *n = *n + 1;

  m = *n;

  for (i = m - 1; i > 0; i--) {
    if (cs[i].distance < cs[i-1].distance) {
      temp = cs[i];
      cs[i] = cs[i-1];
      cs[i-1] = temp;
    }
    else break;
  }
}

static inline 
double distance_squared(double *pta, double *ptb, int dim)
{
  int i;
  double s = 0.0;
  
  for (i=0; i<dim; i++) s += (pta[i] - ptb[i]) * (pta[i] - ptb[i]);

  return s;
}

static 
void 
recurse_neighbours(kdtree_t *tree, int k, c_t *cs, int *n, double *pt, double *dvec)
{
  /*
  static int count = 0;
  
  if (count % 1000 == 0) printf("count %i\n", count);
  count++;
  */

  if (tree->left == NIL) {
    int m = size_set(tree->point_set);
    int i;
    
    for (i=0; i<m; i++) {
      int id = tree->point_set[i];
      double *cpt = ith_map_set(tree->point_set, i);
      
      double dist;

      assert (cpt);

      dist = distance_squared(pt, cpt, tree->k);

      add_element(cs, n, id, cpt, dist);

      if (*n > k) *n = k;
    }
  }
  else {
    int d = tree->d;
    int i;

    if (pt[d] <= tree->x) {
      double old = dvec[d];
      double dist = dvec[d] = tree->x - pt[d];

      recurse_neighbours(tree->left, k, cs, n, pt, dvec);

      if (dist > dvec[d]) dvec[d] = dist;
      dist = 0.0;
            
      for (i=0; i<tree->k; i++) dist += dvec[d] * dvec[d];

      if (*n < k || dist < cs[k-1].distance) recurse_neighbours(tree->right, k, cs, n, pt, dvec);
      dvec[d] = old;	
    }
    else {
      double old = dvec[d];
      double dist = dvec[d] = pt[d] - tree->x;
            
      recurse_neighbours(tree->right, k, cs, n, pt, dvec);

      if (dist > dvec[d]) dvec[d] = dist;
      dist = 0.0;

      for (i=0; i<tree->k; i++) dist += dvec[d] * dvec[d];

      if (*n < k || dist < cs[k-1].distance) recurse_neighbours(tree->left, k, cs, n, pt, dvec);
      dvec[d] = old;
    }
  }
}

/**
 * The closest k neighbours.
 *
 * @param tree a k-d tree.
 * @param k the number of points to choose.
 * @param pt the point to search for.
 *
 * @return a set.
 */

set_t 
closest_k_neighbours(kdtree_t *tree, int k, double *pt)
{
  c_t *cs = (c_t *) malloc((k + 1) * sizeof(c_t));
  set_t result = alloc_set(SP_MAP);
  int n = 0;
  int i;

  double *dvec = calloc(tree->k, sizeof(double));

  recurse_neighbours(tree, k, cs, &n, pt, dvec);

  for (i=0; i<n; i++) 
    result = associate_set(result, cs[i].id, cs[i].pt);

  free(cs);

  return result;  
}
