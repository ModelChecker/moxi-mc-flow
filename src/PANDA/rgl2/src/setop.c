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

set_t copy_set(set_t a)
{
  set_t result = alloc_set(0);
  int size = size_set(a);
  int i;
  for (i=0;i<size;i++) {
    result = put_set(result, a[i]);
  }
  return result;
}

set_t subtract_set(set_t a, set_t b)
{
  set_t result = alloc_set(0);
  int size = size_set(a);
  int i;
  
  for (i=0;i<size;i++) {
    if (!contains_set(b,a[i]))
      result = put_set(result, a[i]);
  }
  return result;
}

set_t union_set(set_t a, set_t b)
{
  set_t result = alloc_set(0);
  int size = size_set(a);
  int i;
  
  for (i=0;i<size;i++) {
      result = put_set(result, a[i]);
  }
  size = size_set(b);
  for (i=0;i<size;i++) {
      result = put_set(result, b[i]);
  }
  return result;
}

set_t intersect_set(set_t a, set_t b)
{
  set_t result = alloc_set(0);
  int size;
  int i;
  size = size_set(a);
  for (i=0;i<size;i++) {
    if (contains_set(b,a[i]))
      result = put_set(result, a[i]);
  }
  return result;
}

