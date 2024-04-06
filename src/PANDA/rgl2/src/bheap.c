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


#include "bheap.h"

#define parent(i)(((i) - 1) / 2)
#define left(i) (2 * (i) + 1)
#define right(i) (2 * (i) + 2)

typedef struct 
{
  cmp_fn_t cmp_fn;
  pointer_t data;  
} bheap_header_t;

/**
 * Allocates a binary heap.
 *
 * @param cmp_fn the comparator for the elements.
 * @param data the data to passed to every comparison call.
 *
 * @return a fresh binary heap.
 */

bheap_t 
alloc_bheap(cmp_fn_t cmp_fn, pointer_t data)
{
  bheap_header_t *header = (bheap_header_t *) malloc(sizeof(bheap_header_t));
  set_t s = alloc_set(0);

  header->cmp_fn = cmp_fn;
  header->data = data;

  set_header_set(s, header);

  return s;
}

/**
 * Frees a binary heap.
 */

void 
free_bheap(bheap_t bh)
{
  free(get_header_set(bh));
  free_set(bh);
}

/**
 * Puts an element into the binary heap.
 *
 * @param bh the binary heap.
 * @param key the key to put.
 *
 * @return a possibly different heap.
 */

bheap_t 
put_bheap(bheap_t bh, int key)
{
  int i = size_set(bh);
  bheap_header_t *header = (bheap_header_t *) get_header_set(bh);
  cmp_fn_t cmp_fn = header->cmp_fn;
  pointer_t data = header->data;

  bh = put_set(bh, key);

  while (i > 0) {
    int p = parent(i);
    int elt = bh[i];
    int pelt = bh[p];

    if (cmp_fn(data, pelt, elt) > 0) {
      swap_set(bh, i, p);
      i = p;
    }
    else break;
  }

  return bh;
}

/**
 * Removes a key from the binary heap.
 *
 * @param bh the binary heap.
 * @param key the key to remove.
 *
 * @return TRUE if something was removed, FALSE otherwise.
 */

boolean_t 
remove_bheap(bheap_t bh, int key)
{
  bheap_header_t *header = (bheap_header_t *) get_header_set(bh);
  cmp_fn_t cmp_fn = header->cmp_fn;
  pointer_t data = header->data;
  
  int n = size_set(bh);
  int i = index_of_set(bh, key);

  if (i == -1) return FALSE;

  /* PAN */
  while (i>0) {
    swap_set(bh, parent(i), i);
    i = parent(i);
  }
  /* END PAN */

  swap_set(bh, i, n - 1);
  remove_set(bh, key);

  n--;

  while (i < n) {
    int l = left(i);
    int r = right(i);
    int elt = bh[i];
    int lelt = bh[l];
    int relt = bh[r];
    int m = i;
    int melt = elt;

    if (l < n && cmp_fn(data, elt, lelt) > 0) { m = l; melt = lelt; }
    if (r < n && cmp_fn(data, melt, relt) > 0) m = r;

    if (i != m) { swap_set(bh, i, m); i = m; }
    else break;
  }

  return TRUE;    
}

/**
 * Removes a key by index.
 *
 * @param bh the binary heap.
 * @param index the index to remove.
 *
 * @return the element that was removed.
 */

int 
remove_by_index_bheap(bheap_t bh, int index)
{
  int key = bh[index];
  
  remove_bheap(bh, key);

  return key;
}

/**
 * Heapsorts an array of elements.  The array 'elts' will return sorted.
 *
 * @param elts an array of elements (keys).
 * @param len the length of the array.
 * @param cmp_fn a comparator.
 * @param data the data for the comparator.
 */

void 
heapsort_bheap(int *elts, int len, cmp_fn_t cmp_fn, pointer_t data)
{
  bheap_t bh = alloc_bheap(cmp_fn, data);

  int i;
  for (i=0; i<len; i++) {
    bh = put_bheap(bh, elts[i]);
    //   pretty_print_set(stdout, bh);    
  }
  for (i=0; i<len; i++) elts[i] = extract_bheap(bh);

  free_bheap(bh);
}
