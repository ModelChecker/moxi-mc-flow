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


#include "serial_ds.h"

set_t 
read_set(unserial_fn_t mapped, unserial_fn_t header)
{
  int size;
  word_t prop;
  int *data;
  set_t s;
  int i;
    
  read_int(size);
  read_int(prop);
  
  data = read_data(sizeof(int) * size);

  s = alloc_set(prop);

  for (i=0; i<size; i++) 
    s = put_set(s, data[i]);

  if (header) {
    set_head_t *sh = get_set_head(s);
    int len;
    pointer_t rawhead;
    
    read_int(len);
    if (len >= 0) {
      rawhead = read_data(len);
    
      sh->header = header(rawhead, len);
    }
    else sh->header = header(NULL, len);
  }

  if ((prop & SP_MAP) && mapped) {
    for (i=0; i<size; i++) {
      pointer_t buf;
      int len;
      
      read_int(len);
      if (len >= 0) {
	buf = read_data(len);

	s = associate_set(s, s[i], mapped(buf, len));
      }
      else 
	s = associate_set(s, s[i], mapped(NULL, len));      
    }
  }

  return s;
}

void 
write_set(set_t s, serial_fn_t mapped, int max_map_len, serial_fn_t header, int max_header_len)
{
  set_head_t *sh = get_set_head(s);

  write_int(sh->size);
  write_int(sh->properties);

  write_data(sizeof(int) * (sh->size), s);
  
  if (header) {
    if (max_header_len >= 0) {
      pointer_t headbuf = malloc(max_header_len);
      int headlen = header(sh->header, headbuf);
      
      write_int(headlen);
      write_data(headlen, headbuf);
      
      free(headbuf);
    }
    else {
      int x = -1;
      write_int(x);
      header(sh->header, NULL);
    }
  }

  if ((sh->properties & SP_MAP) && mapped) {
    if (max_map_len >= 0) {
        pointer_t mapbuf = malloc(max_map_len);
	int i;
	
	for (i=0; i<sh->size; i++) {
	  int len = mapped(ith_map_set(s, i), mapbuf);
	  
	  write_int(len);
	  write_data(len, mapbuf);
	}
	
	free(mapbuf);    
    }
    else {
      int i;
      
      for (i=0; i<sh->size; i++) {
	int x = -1;
	write_int(x);
	mapped(ith_map_set(s, i), NULL);      
      }
    }
  }
}

typedef struct
{
  int num_edges;

  word_t properties;

  set_t front_edges;
  set_t back_edges;
  
  set_t vertices;
} g_t;

static unserial_fn_t edge_unserial;

static pointer_t
read_edge_list(pointer_t buf, int len)
{
  return read_set(edge_unserial, NULL);
}

graph_t 
read_graph(unserial_fn_t vertex, unserial_fn_t edge)
{
  g_t *gr = (g_t *) calloc(1, sizeof(g_t));

  edge_unserial = edge;

  read_int(gr->properties);
  
  gr->front_edges =  (set_t) read_set(read_edge_list, NULL);

  if (GP_VERTEX_SET & gr->properties) 
    gr->vertices = (set_t) read_set(vertex, NULL);
  
  if (GP_BACK_EDGES & gr->properties) {
    int i;
    int n = size_set(gr->front_edges);

    gr->back_edges = alloc_set(SP_MAP);
    
    for (i=0; i<n; i++) {
      set_t edges = (set_t) ith_map_set(gr->front_edges, i);
      int from = gr->front_edges[i];
      
      if (edges) {
	int m = size_set(edges);
	int j;
	
	for (j=0; j<m; j++) {
	  int to = edges[j];
	  set_t jedges = (set_t) mapsto_set(gr->back_edges, to);
	  if (jedges == NULL) jedges = alloc_set(0);
	  jedges = put_set(jedges, from);
	  gr->back_edges = associate_set(gr->back_edges, to, jedges);
	}
      }
    }
  }
  
  if (GP_EDGE_NUMBER & gr->properties) {
    int i;
    int n = size_set(gr->front_edges);
    int ec = 0;

    for (i=0; i<n; i++) {
      set_t edges = (set_t) ith_map_set(gr->front_edges, i);
      ec += size_set(edges);      
    }
    
    gr->num_edges = ec;
  }

  return (graph_t) gr;  
}

static serial_fn_t edge_serial;
static int max_edge_len_serial;

static int 
write_edge_list(pointer_t data, pointer_t bp)
{
  set_t s = (set_t) data;

  write_set(s, edge_serial, max_edge_len_serial, NULL, 0);

  return -1;
}

void 
write_graph(graph_t g, serial_fn_t vertex, int max_vertex_len, serial_fn_t edge, int max_edge_len)
{
  g_t *gr = (g_t *) g;
  
  write_int(gr->properties);
  
  edge_serial = edge;
  max_edge_len_serial = max_edge_len;

  write_set(gr->front_edges, write_edge_list, -1, NULL, 0); 
  
  if (gr->properties & GP_VERTEX_SET) 
    write_set(gr->vertices, vertex, max_vertex_len, NULL, 0);
}
