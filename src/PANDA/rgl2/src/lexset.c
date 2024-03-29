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


#include "lexset.h"

typedef struct {
  size_t elements, allocated;
  int *e;
} l_t;

lex_t
alloc_lexset()
{
  l_t *result = (l_t *)malloc(sizeof(l_t));
  result->elements = 0;
  result->allocated = 4;
  result->e = (int *)malloc(sizeof(int)*4);
  return (lex_t)result;
}

void
free_lexset(lex_t l)
{
  l_t *work = (l_t *)l;
  if (work->e != NULL)
    free(work->e);
  free(work);
}

int index_lexset(lex_t l, int elem)
{
  l_t *work = (l_t *)l;
  int start = 0, end = work->elements;
  int pos = 0; 
  while (start != end) {
    pos = (start+end)>>1;
    if (pos == work->elements)
      return pos;
    if (work->e[pos]>elem)
      start = pos+1;
    else
      end = pos;
  }
  return pos;
}

lex_t
add_lexset(lex_t l, int elem)
{
  int pos = index_lexset(l, elem);
  l_t *work = (l_t*)l;
  int i;
  if (pos != work->elements)
    if (work->e[pos]==elem)
      return l;
  if (work->elements == work->allocated) {
    work->allocated*=2;
    work->e = (int *)realloc(work->e, work->allocated*sizeof(int));
  }
  for (i=work->elements-1;i>=pos;i--)
    work->e[i+1]=work->e[i];
  if (i<0) i=0;
  work->e[i] = elem;
  work->elements++;
  return l;
}

boolean_t contains_lexset(lex_t l, int elem)
{
  int pos = index_lexset(l, elem);
  l_t *work = (l_t*)l;
  if (pos == work->elements)
    return FALSE;
  if (work->e[pos]==elem)
    return TRUE;
  else
    return FALSE;
}

int
compare_lexset(lex_t l1, lex_t l2)
{
  l_t *w1, *w2;
  int i, size;
  w1 = (l_t*)l1;
  w2 = (l_t*)l2;
  size = (w1->elements<w2->elements?w1->elements:w2->elements);
  for (i=0;i<size;i++) {
    if (w1->e[i]<w2->e[i])
      return -1;
    if (w1->e[i]>w2->e[i])
      return 1;
  }
  if (w1->elements<w2->elements)
    return -1;
  if (w1->elements>w2->elements)
    return 1;
  return 0;
}
