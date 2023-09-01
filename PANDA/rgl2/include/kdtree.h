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


#ifndef ____RGL_KDTREE_H___
#define ____RGL_KDTREE_H___

#include "defs.h"
#include "set.h"

BEGIN_C_DECL

/**
 * k-d tree data structure.
 */

typedef struct kd_tree
{
  int k;   // total number of dimensions
  int d;   // the current dimension for the split

  double x;  // the split hyperplane:  x_d = x

  int n;   // bound for the point set size for a leaf
  
  set_t point_set;
  
  struct kd_tree *left;
  struct kd_tree *right;
} kdtree_t;

/**
 * Allocate k-d tree.
 *
 * @param k the maximum dimension of the tree.
 * @param n the maximum size of the point set in a leaf.
 *
 * @return an empty kdtree node.
 */

kdtree_t *alloc_kdtree(int k, int n);

/**
 * Deallocate a k-d tree.  This will trash all the point sets but
 * leave the point data alone.
 *
 * @param tree the tree to deallocate.
 */

void free_kdtree(kdtree_t *tree);

/**
 * Put an element into a k-d tree.  
 *
 * @param tree the tree to insert into.
 * @param pt_id the point id.
 * @param pt a point.
 */

int put_kdtree(kdtree_t *tree, int pt_id, double *pt);

/**
 * Remove an element from the k-d tree.
 *
 * @param tree the tree to remove from.
 * @param pt_id the point id to remove.
 *
 * @return TRUE if a point was removed, FALSE otherwise.
 */

boolean_t remove_kdtree(kdtree_t *tree, int pt_id);

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

kdtree_t *construct_kdtree(int k, int n, int num_pts, int *id, double **pts);

/**
 * Returns the leaf that a given point id occurs in.
 *
 * @param tree the tree to operate on.
 * @param pt_id a point id.
 *
 * @return the leaf containing point id or NIL otherwise.
 */

kdtree_t *leaf_kdtree(kdtree_t *tree, int pt_id);

/**
 * Returns the height of the tree.
 *
 * @param tree the tree to operate on.
 *
 * @return the height.
 */

int height_kdtree(kdtree_t *tree);

/**
 * Rebalance the tree.
 *
 * @param tree the tree to rebalance.
 */

void rebalance_kdtree(kdtree_t *tree);

/**
 * Pretty print tree.
 *
 * @param fp a file pointer.
 * @param tree the tree to print.
 */

void pretty_print_kdtree(FILE *fp, kdtree_t *tree);

END_C_DECL

#endif
