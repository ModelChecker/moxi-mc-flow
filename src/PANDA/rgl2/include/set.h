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


#ifndef _____RGL_SET_H_____
#define _____RGL_SET_H_____

#include "defs.h"

typedef struct 
{
  int capacity;
  int size;
  
  int table_size;

  word_t properties;

  pointer_t header;
} set_head_t;

#define get_set_head(s) (set_head_t *) (((byte_t *) s) - sizeof(set_head_t))


/**
 * A set type which can also be used as an array.  The array should not 
 * written into.
 */

typedef int * set_t;

/**
 * An enumeration of set properties.
 */

typedef enum
  {
    SP_MAP = 0x01            /* Adds a map to the set. */
  } set_properties_t;

#define NO_SUCH_ELEMENT -1

BEGIN_C_DECL

/**
 * Allocates a set object.
 *
 * @param properties a union of set properties masks.
 */

set_t alloc_set(word_t properties);

/**
 * Deallocates a set object.
 */

void free_set(set_t s);

/**
 * Returns the number of elements placed in the set.
 */

int size_set(set_t s);

/**
 * Gets the set header (a pointer that can be freely assigned).
 */

pointer_t get_header_set(set_t s);

/**
 * Sets the set header (a pointer that can be freely assigned).
 */

void set_header_set(set_t s, pointer_t header);

/**
 * Puts an element into the set.
 *
 * @param s a set.
 * @param id the 'id' of the element to put.
 *
 * @return the new set - might be different.
 */

set_t put_set(set_t s, int id);

/**
 * Removes an element from the set.
 *
 * @param s a set.
 * @param id the 'id' of the element to remove.
 *
 * @return TRUE if an element was removed or FALSE if nothing removed.
 */

boolean_t remove_set(set_t s, int id);

/**
 * Swap element.
 *
 * @param s a set.
 * @param i the first index.
 * @param j the second index.
 */

void swap_set(set_t s, int i, int j);

/**
 * Checks to see if a set contains a given element.
 *
 * @param s a set.
 * @param id the 'id' of the element to be contained.
 *
 * @return TRUE if the element in the set or FALSE otherwise.
 */

boolean_t contains_set(set_t s, int id);

/**
 * Returns the index of a given element in the set.
 *
 * @param s a set.
 * @param id the 'id' of the element of a given element.
 *
 * @return the index of the element or NO_SUCH_ELEMENT if no such element exists.
 */

int index_of_set(set_t s, int id);

/**
 * Associates an object with an element.  Requires SP_SET_MAP to be set.
 *
 * @param s a set.
 *
 * @param id the element to associate with.
 * @param obj the object to associate.
 *
 * @return the new set - may be different.
 */

set_t associate_set(set_t s, int id, pointer_t obj);

/**
 * Returns the object mapped to a given element in the set.  Requires SP_SET_MAP to be set.
 *
 * @param s a set.
 *
 * @param id the element to check.
 *
 * @return the object associated with element 'id' or NIL if not possible.
 */
 

pointer_t mapsto_set(set_t s, int id);

/**
 * The object stored at the ith index.  Requires SP_SET_MAP to be set.
 *
 * @param s a set.
 * 
 * @param index the index of the element to use.
 *
 * @return the object associated with the indexth element.
 */

static inline 
pointer_t 
ith_map_set(set_t s, int index)
{
  set_head_t *sh = get_set_head(s);
  int cap = sh->capacity;
  int tsz = sh->table_size;

  int *ht = s + cap;
  int *bt = ht + tsz;

  pointer_t *mt = (pointer_t *) (bt + tsz);

  assert (sh->properties & SP_MAP);

  return mt[index];
}

//pointer_t ith_map_set(set_t s, int index);

/**
 * Returns an array of objects associated in the set.  Requires SP_SET_MAP to be set.
 *
 * @param s a set.
 *
 * @return an array of objects.
 */

pointer_t * maptable_set(set_t s);

/**
 * Writes a set in human readable.
 *
 * @param fp a file pointer.
 * @param s a set.
 */

void pretty_print_set(FILE *fp, set_t s);

/**
 * Standard set operations. Any maps are not preserved
 */

set_t copy_set(set_t a);
set_t union_set(set_t a, set_t b);
set_t intersect_set(set_t a, set_t b);
set_t subtract_set(set_t a, set_t b);

END_C_DECL

#endif
