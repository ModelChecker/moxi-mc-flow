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


#include "fbheap.h"

typedef struct
{
  int capacity;
  int size;
  cmp_fn_t cmp_fn;
  pointer_t data;
} f_h_t;

#define get_header(heap)(f_h_t *)(((char *) heap) - sizeof(f_h_t))

#define parent(i)(((i) - 1) / 2)
#define left(i) (2 * (i) + 1)
#define right(i) (2 * (i) + 2)

#define INITIAL_SIZE 8

/**
 * Allocates an fast binary heap.
 *
 * @param cmp_fn a comparator.
 * @param data to be passed to the comparator.
 *
 * @return a fresh heap.
 */

fbheap_t 
alloc_fbheap(cmp_fn_t cmp_fn, pointer_t data)
{
  pointer_t raw = malloc(sizeof(f_h_t) + sizeof(int) * INITIAL_SIZE);
  f_h_t *head = (f_h_t *) raw;
  fbheap_t heap = (fbheap_t) ((char *)raw + sizeof(f_h_t));

  head->capacity = INITIAL_SIZE;
  head->size = 0;
  head->cmp_fn = cmp_fn;
  head->data = data;

  return heap;
}

/**
 * Frees a fast binary heap.
 */

void 
free_fbheap(fbheap_t heap)
{
  f_h_t *head = get_header(heap);

  free(head);
}

/**
 * Size of a fast binary heap.
 */

int 
size_fbheap(fbheap_t heap)
{
  f_h_t *head = get_header(heap);

  return head->size;
}

/**
 * Puts a key into a fast binary heap.  Note a single key can be added multiple times.
 *
 * @param heap the heap
 * @param key a key.
 *
 * @return the new fast binary heap (might be different).
 */

fbheap_t 
put_fbheap(fbheap_t heap, int key)
{
  f_h_t *head = get_header(heap);
  cmp_fn_t cmp_fn = head->cmp_fn;
  pointer_t data = head->data;
  int n = head->size;
  int i = n;

  if (n == head->capacity) {
    int cap = 2 * head->capacity;
    head = (f_h_t *) realloc(head, sizeof(int) * cap + sizeof(f_h_t));
    heap = (int *) (((char *) head) + sizeof(f_h_t));

    head->capacity = cap;
  }

  while (i > 0) {
    int p = parent(i);
    int pelt = heap[p];

    if (cmp_fn(data, pelt, key) <= 0) break;
    
    heap[i] = pelt;
    i = p;
  }

  head->size++;

  heap[i] = key;

  return heap;
}

/**
 * Extracts an element from a fast binary heap.
 *
 * @return the element extracted.
 */

int 
extract_fbheap(fbheap_t heap)
{
  f_h_t *head = get_header(heap);
  cmp_fn_t cmp_fn = head->cmp_fn;
  pointer_t data = head->data;
  int n = head->size - 1;
  int i = 0;
  int elt = heap[0];
  int key = heap[n];

  assert(n >= 0);
  
  while (1) {
    int l = left(i);
    int r = right(i);
    int m = i;
    int melt = key;

    if (l < n && cmp_fn(data, melt, heap[l]) > 0) { m = l; melt = heap[l]; }
    if (r < n && cmp_fn(data, melt, heap[r]) > 0) { m = r; melt = heap[r]; }

    heap[i] = melt;

    if (m == i) break;
    else i = m;
  }
  
  head->size = n;
  
  return elt;  
}

/**
 * Heapsort with fast binary heaps.
 */

void 
heapsort_fbheap(int *elts, int len, cmp_fn_t cmp_fn, pointer_t data)
{
  fbheap_t heap = alloc_fbheap(cmp_fn, data);
  int i;
  
  for (i=0; i<len; i++) heap = put_fbheap(heap, elts[i]);
  for (i=0; i<len; i++) elts[i] = extract_fbheap(heap);

  free_fbheap(heap);
}
