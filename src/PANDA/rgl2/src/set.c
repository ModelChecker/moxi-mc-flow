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


#include "set.h"
#include "prime.h"


#define RATIO 2                /* hash ratio */
#define INITIAL_SIZE 4         /* default initial size for a set */

#define EMPTY -1
#define REMOVED -2

/*
 * set head
 * capacity integers
 * RATIO * capacity integers (hash table)
 * RATIO * capacity integers (back pointers)
 * capacity pointers (optional - for set map)
 *
 */

static set_t 
alloc_set_inner(word_t properties, int sz);

/**
 * Allocates a set object.
 *
 * @param properties a union of set properties masks.
 */

set_t
alloc_set(word_t properties) { return alloc_set_inner(properties, INITIAL_SIZE); }

static set_t 
alloc_set_inner(word_t properties, int c)
{
  int tsz = next_prime(RATIO * c);
  size_t sz = sizeof(set_head_t) + c * sizeof(int) + 2 * tsz * sizeof(int);
  pointer_t ptr;
  set_t s;
  set_head_t *sh;
  int *bp;
  int i;

  if (properties & SP_MAP) sz += c * sizeof(pointer_t);

  ptr = malloc(sz);
  memset(ptr, 0, sz);

  sh = (set_head_t *) ptr;
  s = (set_t) ((char*)ptr + sizeof(set_head_t));

  bp = (int *) ((char *)ptr + sizeof(set_head_t) + c * sizeof(int) + tsz * sizeof(int));

  for (i=0; i<tsz; i++) bp[i] = -1;

  sh->capacity = c;
  sh->table_size = tsz;
  sh->properties = properties;
  sh->header = NULL;

  return s;
}

/**
 * Deallocates a set object.
 */

void 
free_set(set_t s)
{
  set_head_t *sh = get_set_head(s);
  free(sh);
}

/**
 * Returns the number of elements placed in the set.
 */

int 
size_set(set_t s)
{
  set_head_t *sh = get_set_head(s);

  return sh->size;
}

static inline 
int 
probe(int *ht, int *bt, int c, int tsz, int id)
{
  int i;
  int index = EMPTY;

  for (i=0; i<c; i++) {
    int k = (abs(id) + i * i) % tsz;

    if (index == EMPTY && bt[k] < 0) index = k;
    if (bt[k] == EMPTY) return index;
    if (ht[k] == id) return k;
  }

  //  assert ("error in probe function - hash table full" == 0);

  return index;
}

/**
 * Gets the set header (a pointer that can be freely assigned).
 */

pointer_t
get_header_set(set_t s)
{
  set_head_t *sh = get_set_head(s);

  return sh->header;
}

/**
 * Sets the set header (a pointer that can be freely assigned).
 */

void 
set_header_set(set_t s, pointer_t header)
{
  set_head_t *sh = get_set_head(s);
  
  sh->header = header;
}


/**
 * Puts an element into the set.
 *
 * @param s a set.
 * @param id the 'id' of the element to put.
 *
 * @return the new set - might be different.
 */

set_t 
put_set(set_t s, int id)
{
  set_head_t *sh = get_set_head(s);
  int cap = sh->capacity;
  int sz = sh->size;
  int tsz = sh->table_size;

  int *ht = s + cap;
  int *bt = ht + tsz;

  int index;

  if (sz == cap) {
    set_t ns = alloc_set_inner(sh->properties, sz * 2);

    int i;

    if (sh->properties & SP_MAP) {
      pointer_t *mt = (pointer_t *) (bt + tsz);

      for (i=0; i<sz; i++) associate_set(ns, s[i], mt[i]);
    }
    else 
      for (i=0; i<sz; i++) put_set(ns, s[i]);

    set_header_set(ns, sh->header);

    free_set(s);    

    return put_set(ns, id);
  }

  index = probe(ht, bt, cap, tsz, id);
  
  if (index < 0) {
    pretty_print_set(stderr, s);
    fprintf(stderr, "id: %i\n", id);
  }
  assert (index >= 0);

  if (ht[index] == id && bt[index] >= 0) return s;

  s[sz] = id;
  ht[index] = id;
  bt[index] = sz;

  sh->size ++;

  return s;
}

/**
 * Removes an element from the set.
 *
 * @param s a set.
 * @param id the 'id' of the element to remove.
 *
 * @return TRUE if an element was removed or FALSE if nothing removed.
 */

boolean_t 
remove_set(set_t s, int id)
{
  set_head_t *sh = get_set_head(s);
  int cap = sh->capacity;
  int sz = sh->size;
  int tsz = sh->table_size;

  int *ht = s + cap;
  int *bt = ht + tsz;

  int index = probe(ht, bt, cap, tsz, id);

  if (ht[index] == id && bt[index] >= 0) {
    int index_end = probe(ht, bt, cap, tsz, s[sz - 1]);
    
    bt[index_end] = bt[index];
    
    s[bt[index]] = s[sz - 1];

    if (sh->properties & SP_MAP) {
      pointer_t *mt = (pointer_t *) (bt + tsz);

      mt[bt[index]] = NIL;
    }

    bt[index] = REMOVED;

    sh->size--;

    return TRUE;
  }
  else return FALSE;
}

/**
 * Swap element.
 *
 * @param s a set.
 * @param i the first index.
 * @param j the second index.
 */

void 
swap_set(set_t s, int i, int j)
{
  set_head_t *sh = get_set_head(s);
  int cap = sh->capacity;
  int tsz = sh->table_size;

  int *ht = s + cap;
  int *bt = ht + tsz;

  pointer_t *mt = (pointer_t) (bt + tsz);

  int n = sh->size;

  int indexA = probe(ht, bt, cap, tsz, s[i]);
  int indexB = probe(ht, bt, cap, tsz, s[j]);
  
  int temp;
  pointer_t dummy;

  assert (i >= 0 && i < n);
  assert (j >= 0 && j < n);
  
  temp = s[i];
  s[i] = s[j];
  s[j] = temp;

  bt[indexA] = j;
  bt[indexB] = i;

  if (SP_MAP & sh->properties) {
    dummy = mt[i];
    mt[i] = mt[j];
    mt[j] = dummy;
  }
}

/**
 * Checks to see if a set contains a given element.
 *
 * @param s a set.
 * @param id the 'id' of the element to be contained.
 *
 * @return TRUE if the element in the set or FALSE otherwise.
 */

boolean_t 
contains_set(set_t s, int id)
{
  set_head_t *sh = get_set_head(s);
  int cap = sh->capacity;
  int tsz = sh->table_size;

  int *ht = s + cap;
  int *bt = ht + tsz;

  int index = probe(ht, bt, cap, tsz, id);
  
  if (index == EMPTY) return FALSE;
  else if (ht[index] == id && bt[index] >= 0) return TRUE;
  else return FALSE;
}

/**
 * Returns the index of a given element in the set.
 *
 * @param s a set.
 * @param id the 'id' of the element of a given element.
 *
 * @return the index of the element or NO_SUCH_ELEMENT if no such element exists.
 */

int 
index_of_set(set_t s, int id)
{
  set_head_t *sh = get_set_head(s);
  int cap = sh->capacity;
  int tsz = sh->table_size;

  int *ht = s + cap;
  int *bt = ht + tsz;

  int index = probe(ht, bt, cap, tsz, id);

  if (ht[index] == id && bt[index] >= 0) return bt[index];
  else return EMPTY;
}

/**
 * Associates an object with an element.  Requires SP_SET_MAP to be set.
 *
 * @param s a set.
 *
 * @param id the element to associate with.
 * @param obj the object to associate. 
 *
 * @return the new set - might be different.
 */

set_t 
associate_set(set_t s, int id, pointer_t obj)
{
  set_head_t *sh = get_set_head(s);
  
  int cap = sh->capacity;
  int tsz = sh->table_size;

  int *ht = s + cap;
  int *bt = ht + tsz;

  pointer_t *mt = (pointer_t *) (bt + tsz);
  
  int index = probe(ht, bt, cap, tsz, id);
  
  assert (sh->properties & SP_MAP);
  
  if (index == EMPTY || bt[index] < 0) {
    s = put_set(s, id);
    
    sh = get_set_head(s);
    
    cap = sh->capacity;
    tsz = sh->table_size;
    
    ht = s + cap;
    bt = ht + tsz;
    
    mt = (pointer_t *) (bt + tsz);
    
    index = probe(ht, bt, cap, tsz, id);
    
    if (index == EMPTY) {
      pretty_print_set(stderr, s);
      fprintf(stderr, "id: %i\n", id);
    }
    assert (index != EMPTY);
  }

  mt[bt[index]] = obj;

  return s;
}

/**
 * Returns the object mapped to a given element in the set.  Requires SP_SET_MAP to be set.
 *
 * @param s a set.
 *
 * @param id the element to check.
 *
 * @return the object associated with element 'id' or NIL if not possible.
 */
 
pointer_t 
mapsto_set(set_t s, int id)
{
  set_head_t *sh = get_set_head(s);
  int cap = sh->capacity;
  int tsz = sh->table_size;

  int *ht = s + cap;
  int *bt = ht + tsz;

  pointer_t *mt = (pointer_t *) (bt + tsz);
  int index = probe(ht, bt, cap, tsz, id);

  assert (sh->properties & SP_MAP);
  
  if (ht[index] == id && bt[index] >= 0) return mt[bt[index]];
  else return NIL;  
}

/**
 * The object stored at the ith index.  Requires SP_SET_MAP to be set.
 *
 * @param s a set.
 * 
 * @param index the index of the element to use.
 *
 * @return the object associated with the indexth element.
 */


/**
 * Returns an array of objects associated in the set.  Requires SP_SET_MAP to be set.
 *
 * @param s a set.
 *
 * @return an array of objects.
 */

pointer_t * 
maptable_set(set_t s)
{
  set_head_t *sh = get_set_head(s);
  int cap = sh->capacity;
  int tsz = sh->table_size;

  int *ht = s + cap;
  int *bt = ht + tsz;

  pointer_t *mt = (pointer_t *) (bt + tsz);

  return mt;
}


/**
 * Writes a set in human readable.
 *
 * @param fp a file pointer.
 * @param s a set.
 */

void
pretty_print_set(FILE *fp, set_t s)
{
  set_head_t *sh = get_set_head(s);
  int cap = sh->capacity;
  int sz = sh->size;
  int tsz = sh->table_size;

  int *ht = s + cap;
  int *bt = ht + tsz;

  pointer_t *mt = (pointer_t *) (bt + tsz);
  int i;
  
  fprintf(fp, "cap: %i size: %i table_size: %i prop: %x\n", cap, sz, tsz, sh->properties);
  
  for (i=0; i<cap; i++) fprintf(fp, "%i ", s[i]);
  fprintf(fp, "\n");

  for (i=0; i<tsz; i++) fprintf(fp, "%i ", ht[i]);
  fprintf(fp, "\n");

  for (i=0; i<tsz; i++) fprintf(fp, "%i ", bt[i]);
  fprintf(fp, "\n");

  if (sh->properties & SP_MAP) {
    for (i=0; i<cap; i++) fprintf(fp, "%x ", (int) (mt[i]));
    fprintf(fp, "\n");
  }  
}

