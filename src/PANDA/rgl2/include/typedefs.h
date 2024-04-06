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


#ifndef TYPEDEFS_H
#define TYPEDEFS_H

#include <stdbool.h>
#include <sys/types.h>
#include <unistd.h>

#ifndef UINT_T
#define UINT_T
typedef unsigned int uint_t;
#endif

typedef enum workmode {
  WRING, 
  SPIN, 
  FINITESPIN,
  CADENCE, 
  NUSMV
} workmode_t;

typedef enum traversal {
  FORWARD,
  BACKWARD
} traversal_t;

typedef enum heuristic {
  MCS,
  LEXP,
  LEXM,
  LINEAR,
  DEFAULT
} heuristic_t;


typedef enum mcs_start {
  MIN,
  MAX,
  ZERO,
  RANDOM
} mcs_start_t;

typedef enum transition_encoding {
  SLOPPY,
  FUSSY
} enc_t;


typedef enum rank_change {
  JUMP,
  CRAWL
} rank_change_t;


typedef enum ord_sty {
  INTERLEAVE,
  FOLLOW
} order_style_t;


typedef enum ord_ord {
  RANKSUBSET,
  SUBSETRANK
} order_order_t;


typedef struct automaton_params { /*only need 2 parts:*/
    uint_t automaton_size; /*number of nodes in graph*/
    uint_t num_letters;
    uint_t num_letter_bits;
    bool*** transitions; /*matrix with a 1 where there's an edge*/
    bool* accepting_states;
}* automaton_params_t;



struct parameters { /*pass tie-breaking variables in here and any other global vars*/

  /* Execution */
  uint_t rank;
  uint_t procs;
  uint_t debug;
  uint_t verbosity;
  workmode_t workmode;
  bool singleFileMode;
  bool translateMode;
  char* singleFileName;
  char* translateOut;
  int timeout;

  /* Execution flags */
  char* pan_flags;
  char* spin_flags;
  char* wring_flags;

  /* Directories */
  char* src;
  char* dest;
  char* tmp;
  char* wring_dir;

  /* Commands */
  char* wring_cmd;
  char* spin_cmd;
  char* cadence_cmd;
  char* nusmv_cmd;
  char* gcc_cmd;

  /* Heuristics */
  heuristic_t heuristic;
  uint_t heuristic_reverse;
  mcs_start_t mcs_start_node;
  order_style_t order_style;
  order_order_t order_order;

  /* Optimizations */
  traversal_t traversal;
  uint_t use_force;
  uint_t mono;
  uint_t spin_sanity;
  uint_t smv_sanity;
  enc_t rank_encoding;
  enc_t obligation_encoding;
  rank_change_t rank_change;
  uint_t incremental;
  uint_t maxrank;
  uint_t fixed_rank;

  /* Internal variables */
  bool** A_copy;
  bool** B_copy;
  automaton_params_t automaton_params;
  char* logfile;
  //pid_t child_pid;
};

typedef struct parameters* params_t;

#endif
