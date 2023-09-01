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


#include "kdtree.h"

/**
 * Allocate k-d tree.
 *
 * @param k the maximum dimension of the tree.
 * @param n the maximum size of the point set in a leaf.
 *
 * @return an empty kdtree node.
 */

kdtree_t *
alloc_kdtree(int k, int n)
{
  kdtree_t *tree = (kdtree_t *) malloc(sizeof(kdtree_t));

  tree->k = k;
  tree->d = 0;
  
  tree->n = n;

  tree->point_set = alloc_set(SP_MAP);
  
  tree->left = NIL;
  tree->right = NIL;

  return tree;
}

/**
 * Deallocate a k-d tree.  This will trash all the point sets but
 * leave the point data alone.
 *
 * @param tree the tree to deallocate.
 */

void 
free_kdtree(kdtree_t *tree)
{
  if (tree->left) free_kdtree(tree->left);
  if (tree->right) free_kdtree(tree->right);

  free_set(tree->point_set);

  free(tree);
}

/**
 * Put an element into a k-d tree.  
 *
 * @param tree the tree to insert into.
 * @param pt_id the point id.
 * @param pt a point.
 */

int 
put_kdtree(kdtree_t *tree, int pt_id, double *pt)
{
  if (contains_set(tree->point_set, pt_id)) return -1;

  tree->point_set = associate_set(tree->point_set, pt_id, pt);
  
  if (tree->left == NIL) {
    if (size_set(tree->point_set) == tree->n) {
      rebalance_kdtree(tree);
      return 1;
    }
    else return 0;
  }
  else {
    int d = tree->d;
    int h;
    int cap;
    int n;
    
    /*static int max_observed = 0;*/

    if (pt[d] <= tree->x) h = put_kdtree(tree->left, pt_id, pt);
    else h = put_kdtree(tree->right, pt_id, pt);

    if (h == -1) return -1;

    n = size_set(tree->point_set);
    h = h + 1;
    cap = (1 << h) * tree->n;

    if (cap / n > 3) {
      free_kdtree(tree->left);
      free_kdtree(tree->right);
      tree->left = NIL;
      tree->right = NIL;
      
      rebalance_kdtree(tree);
      
      return -1;
    }
    return h;
  }
}

/**
 * Remove an element from the k-d tree.
 *
 * @param tree the tree to remove from.
 * @param pt_id the point id to remove.
 *
 * @return TRUE if a point was removed, FALSE otherwise.
 */

boolean_t 
remove_kdtree(kdtree_t *tree, int pt_id)
{    
  double *pt = (double *) mapsto_set(tree->point_set, pt_id);

  if (pt != NIL) {
    int d = tree->d;
    
    remove_set(tree->point_set, pt_id);

    if (tree->left == NIL) return TRUE;
    else if (pt[d] <= tree->x) {
      boolean_t result = remove_kdtree(tree->left, pt_id);
      
      assert (result == TRUE);
      
      return TRUE;
    }
    else {
      boolean_t result = remove_kdtree(tree->right, pt_id);

      assert (result == TRUE);

      return TRUE;
    }
  }
  else return FALSE;
}

/**
 * Construct a k-d tree from an array of points.
 *
 * @param k the maximum dimension of the tree.
 * @param n the maximum size of the point set in a leaf.
 * @param num_pts size of the arrays.
 * @param id an array of point ids.
 * @param pts an array of points.
 *
 * @return the constructed k-d tree.
 */

kdtree_t *
construct_kdtree(int k, int n, int num_pts, int *id, double **pts)
{
  kdtree_t *tree = alloc_kdtree(k, n);
  int i;

  for (i=0; i<num_pts; i++) 
    tree->point_set = associate_set(tree->point_set, id[i], pts[i]);
  
  rebalance_kdtree(tree);
  
  //printf("tree is height %i\n", height_kdtree(tree));
  
  return tree;  
}

/**
 * Returns the leaf that a given point id occurs in.
 *
 * @param tree the tree to operate on.
 * @param pt_id a point id.
 *
 * @return the leaf containing point id or NIL otherwise.
 */

kdtree_t *
leaf_kdtree(kdtree_t *tree, int pt_id)
{
  double *pt = (double *) mapsto_set(tree->point_set, pt_id);
  int d = tree->d;
  
  if (pt == NIL) return NIL;

  if (tree->left == NIL) return tree;

  if (pt[d] <= tree->x) return leaf_kdtree(tree->left, pt_id);
  else return leaf_kdtree(tree->right, pt_id);
}

/**
 * Returns the height of the tree.
 *
 * @param tree the tree to operate on.
 *
 * @return the height.
 */

int 
height_kdtree(kdtree_t *tree)
{
  if (tree->left == NIL) return 1;
  else {
    int lh = height_kdtree(tree->left);
    int rh = height_kdtree(tree->right);

    if (lh < rh) return rh + 1;
    else return lh + 1;
  }
}

typedef struct 
{
  int id;
  double *pt;
} pt_s_t;

static int cmp_d;

int 
cmp_pt_s(const void *a, const void *b)
{
  pt_s_t *pa = (pt_s_t *) a;
  pt_s_t *pb = (pt_s_t *) b;

  if (pa->pt[cmp_d] <= pb->pt[cmp_d]) return -1;
  else if (pa->pt[cmp_d] == pb->pt[cmp_d]) return 0;
  else return 1;
}

/**
 * Rebalance the tree.
 *
 * @param tree the tree to rebalance.
 */

void 
rebalance_kdtree(kdtree_t *tree)
{
  int n = size_set(tree->point_set);
  int m = n / 2;
  int d = tree->d;
  pt_s_t *pts;
  int i;

  if (tree->left) free_kdtree(tree->left);
  if (tree->right) free_kdtree(tree->right);

  tree->left = NIL;
  tree->right = NIL;

  if (n < tree->n) return;

  pts = (pt_s_t *) malloc(sizeof(pt_s_t) * n);

  for (i=0; i<n; i++) {
    pts[i].id = tree->point_set[i];
    pts[i].pt = ith_map_set(tree->point_set, i);
  }
  
  cmp_d = d;

  qsort(pts, n, sizeof(pt_s_t), cmp_pt_s);
  /*
  printf("------------\n");
  for (i=0; i<n; i++) {
    for (j=0; j<tree->k; j++) printf("%f ", pts[i].pt[j]);
    printf("\n");
  }
  */

  while (m < n-1 && pts[m].pt[d] == pts[m+1].pt[d]) m++;

  tree->left = alloc_kdtree(tree->k, tree->n);
  tree->right = alloc_kdtree(tree->k, tree->n);

  tree->left->d = (tree->d + 1) % tree->k;
  tree->right->d = (tree->d + 1) % tree->k;

  for (i=0; i<m; i++) 
    tree->left->point_set = associate_set(tree->left->point_set, pts[i].id, pts[i].pt);    
  
  for (i=m; i<n; i++) 
    tree->right->point_set = associate_set(tree->right->point_set, pts[i].id, pts[i].pt);
    
  tree->x = pts[m].pt[d];

  free(pts);

  rebalance_kdtree(tree->left);
  rebalance_kdtree(tree->right);
}


/**
 * Pretty print tree.
 *
 * @param fp a file pointer.
 * @param tree the tree to print.
 */

void 
pretty_print_kdtree(FILE *fp, kdtree_t *tree)
{
  int n = size_set(tree->point_set);
  int i;

  fprintf(fp, "%x\n", (int) tree);
  
  for (i=0; i<n; i++)
    fprintf(fp, "%i ", tree->point_set[i]);

  fprintf(fp, "\n");

  if (tree->left) {
    fprintf(fp, "LEFT\n");
    pretty_print_kdtree(fp, tree->left);
    fprintf(fp, "RIGHT\n");
    pretty_print_kdtree(fp, tree->right);
  }
}
