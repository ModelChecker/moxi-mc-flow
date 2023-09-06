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


#ifndef ___RGL_BHEAP__H___
#define ___RGL_BHEAP__H___

#include "set.h"

BEGIN_C_DECL

/**
 * Minimizing binary heaps.
 */

typedef set_t bheap_t;

/**
 * A comparison function.  It takes some data and two keys.  Usual convention for
 * comparators: -1 for less than, 0 for equals, 1 for greater than.
 */

typedef int (*cmp_fn_t)(pointer_t, int, int);

/**
 * Allocates a binary heap.
 *
 * @param cmp_fn the comparator for the elements.
 * @param data the data to passed to every comparison call.
 *
 * @return a fresh binary heap.
 */

bheap_t alloc_bheap(cmp_fn_t cmp_fn, pointer_t data);

/**
 * Frees a binary heap.
 */

void free_bheap(bheap_t bh);

/**
 * Gets the size of binary heap.
 */

#define size_bheap(bh) size_set(bh)

/**
 * Puts an element into the binary heap.
 *
 * @param bh the binary heap.
 * @param key the key to put.
 *
 * @return a possibly different heap.
 */

bheap_t put_bheap(bheap_t bh, int key);

/**
 * Removes a key from the binary heap.
 *
 * @param bh the binary heap.
 * @param key the key to remove.
 *
 * @return TRUE if something was removed, FALSE otherwise.
 */

boolean_t remove_bheap(bheap_t bh, int key);

/**
 * Removes a key by index.
 *
 * @param bh the binary heap.
 * @param index the index to remove.
 *
 * @return the element that was removed.
 */

int remove_by_index_bheap(bheap_t bh, int index);

/**
 * Removes the key with index 0 and returns it.
 */

#define extract_bheap(bh) remove_by_index_bheap(bh, 0)

/**
 * Peeks at the key with index 0.
 */

#define top_bheap(bh) bh[0]

/**
 * Membership check for a given key.
 */

#define member_bheap(bh,key) member_set(bh,key)

/**
 * Heapsorts an array of elements.  The array 'elts' will return sorted.
 *
 * @param elts an array of elements (keys).
 * @param len the length of the array.
 * @param cmp_fn a comparator.
 * @param data the data for the comparator.
 */

void heapsort_bheap(int *elts, int len, cmp_fn_t cmp_fn, pointer_t data);

END_C_DECL

#endif
