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


#ifndef ___RGL_FBHEAP_H___
#define ___RGL_FBHEAP_H___

#include "bheap.h"

BEGIN_C_DECL

/**
 * Faster minimizing binary heaps that do not support look up operations.
 */

typedef int * fbheap_t;

/**
 * Allocates an fast binary heap.
 *
 * @param cmp_fn a comparator.
 * @param data to be passed to the comparator.
 *
 * @return a fresh heap.
 */

fbheap_t alloc_fbheap(cmp_fn_t cmp_fn, pointer_t data);

/**
 * Frees a fast binary heap.
 */

void free_fbheap(fbheap_t heap);

/**
 * Size of a fast binary heap.
 */

int size_fbheap(fbheap_t heap);

/**
 * Puts a key into a fast binary heap.  Note a single key can be added multiple times.
 *
 * @param heap the heap
 * @param key a key.
 *
 * @return the new fast binary heap (might be different).
 */

fbheap_t put_fbheap(fbheap_t heap, int key);

/**
 * Extracts an element from a fast binary heap.
 *
 * @return the element extracted.
 */

int extract_fbheap(fbheap_t heap);

/**
 * Returns the smallest element in the heap.
 */

int top_fbheap(fbheap_t heap);

/**
 * Heapsort with fast binary heaps.
 */

void heapsort_fbheap(int *elts, int len, cmp_fn_t cmp_fn, pointer_t data);

END_C_DECL

#endif
