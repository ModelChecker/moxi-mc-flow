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


#include "prime.h"

#define MAX_NUMBER 65536
#define MAX_NUM_PRIMES 65536

static int erato_table[MAX_NUM_PRIMES];
static int total_primes = 0;

static void 
fill_table()
{
  int table[MAX_NUMBER];
  int i;
  
  for (i=0; i<MAX_NUMBER; i++) table[i] = 0;

  for (i=2; i<MAX_NUMBER; i++) 
    if (table[i] == 0) {
      int j;
      
      for (j=2*i; j<MAX_NUMBER; j+=i) table[j] = 1;
    }
  
  for (i=2; i<MAX_NUMBER; i++)
    if (table[i] == 0) erato_table[total_primes++] = i;
}


boolean_t 
is_prime(int n)
{
  int i;

  if (total_primes == 0) fill_table();

  for (i=0; i<total_primes; i++) {
    if (n % erato_table[i] == 0) return FALSE;
    if (erato_table[i] * erato_table[i] > n) return TRUE;
  }

  return TRUE;
}

int 
next_prime(int n)
{
  while (1) {
    if (is_prime(n)) return n;
    else n++;
  }

  assert ("impossible - next prime failed" == 0);

  return 0;
}
