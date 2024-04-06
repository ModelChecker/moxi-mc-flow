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


#include <stdlib.h>
#include "fast_union.h"


/**
 * Allocates a fast union object.
 */

fast_union_t *
alloc_fast_union(int id)
{
  fast_union_t *ft = malloc(sizeof(fast_union_t));

  ft->rank = 0;
  ft->id = id;
  ft->parent = NULL;

  return ft;
}

/**
 * Frees a fast union object.
 */

void 
free_fast_union(fast_union_t *fu)
{
  free(fu);
}


static inline
fast_union_t *findset(fast_union_t *fu)
{
  fast_union_t *r;

  if (fu->parent == NULL) return fu;
  
  r = findset(fu->parent);
  fu->parent = r;

  return r;
}

static inline
void link(fast_union_t *a, fast_union_t *b)
{
  if (a == b) return;
  else if (a->rank > b->rank) b->parent = a;
  else {
    a->parent = b;
    if (a->rank == b->rank) b->rank++;
  }
}

/**
 * Computes the union between two sets.
 */

void 
union_fast_union(fast_union_t *a, fast_union_t *b)
{
  link(findset(a), findset(b));
}

/**
 * Returns the representative of two unions.
 */

int 
representative_fast_union(fast_union_t *fu)
{
  fast_union_t *p = findset(fu);

  return p->id;
}
