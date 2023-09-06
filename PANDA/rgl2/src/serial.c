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


#include "serial.h"

#include <assert.h>

static FILE *the_fp = NULL;
static boolean_t reading = TRUE;
static pointer_t the_buffer = NULL;
static int read_size;
static int buffer_size;
static int buffer_index;

static inline
void read_buffer(void)
{
  assert (reading);
  assert (the_fp);

  buffer_size = fread(the_buffer, 1, read_size, the_fp);

  if (buffer_size < read_size) {
    the_fp = NULL;
  }

  buffer_index = 0;
}

void 
begin_read(FILE *fp, int max_buffer)
{
  assert (the_fp == NULL); 
  assert (the_buffer == NULL);

  the_fp = fp;

  the_buffer = malloc(max_buffer);
  read_size = max_buffer;
  reading = TRUE;

  read_buffer();
}

void 
end_read(void)
{
  the_fp = NULL;
  free(the_buffer);
  the_buffer = NULL;
}

pointer_t 
read_data(int len)
{
  pointer_t ret;
  
  assert (len <= buffer_size);

  if (len + buffer_index > buffer_size) {
    pointer_t bufbegin;
    int headsize = buffer_size - buffer_index;
    
    memmove(the_buffer, (char *)the_buffer + buffer_index, buffer_size - buffer_index);
    
    bufbegin = the_buffer;
    read_size = buffer_index;
    the_buffer = (char *)the_buffer + headsize;

    read_buffer();
    the_buffer = bufbegin;
    buffer_size += headsize;
    read_size += headsize;
  }

  ret = (char *)the_buffer + buffer_index;
  buffer_index += len;

  return ret;
}

void 
read_data_copy(int len, pointer_t buffer)
{
  pointer_t ptr = read_data(len);

  memcpy(buffer, ptr, len);
}

static inline
void flush_write(void)
{
  assert (reading == FALSE);
  assert (the_fp);
  assert (the_buffer);

  if (buffer_index > 0) {
    fwrite(the_buffer, 1, buffer_index, the_fp);
    buffer_index = 0;
  }
}

void 
begin_write(FILE *fp, int max_buffer)
{
  assert (the_fp == NULL);
  assert (the_buffer == NULL);

  the_fp = fp;
  reading = FALSE;
  
  the_buffer = malloc(max_buffer);

  buffer_size = max_buffer;
}

void 
end_write(void)
{
  flush_write();
  the_fp = NULL;
  free(the_buffer);
  the_buffer = NULL;
}

void 
write_data(int len, pointer_t data)
{
  assert (the_fp);
  assert (reading == FALSE);
  assert (the_buffer);
  
  if (len > buffer_size) {	    
    fwrite(data, 1, len, the_fp);
    
    return;
  }
  if (len > buffer_size - buffer_index) flush_write();

  memcpy((char *)the_buffer + buffer_index, data, len);

  buffer_index += len;  
}
