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


#ifndef __CONF__H__
#define __CONF__H__

#include <stdio.h>

#include "defs.h"

BEGIN_C_DECL

/** 
 * Reads in a configuration file.  Reads are additive and copy over.
 *
 * @param fp a file pointer to the file.
 *
 * @return the number of variables read or -1 on an error.
 */

int read_conf(FILE *fp);

/**
 * Writes a configuration file from the current state of the machine.
 *
 * @param fp a file pointer to the file.
 *
 * @return the number of variables written or -1 on an error.
 */

int write_conf(FILE *fp);

/**
 * Checks if a variable is set.
 *
 * @param name the name of the variable.
 *
 * @return TRUE if the variable is set and false otherwise.
 */

boolean_t check_variable_conf(string_t name);

/**
 * Read double variable.
 *
 * @param name the name of the variable.
 * @param def a default value for the variable.
 *
 * @return the value if set or the default value if not set.
 */

double read_double_conf(string_t name, double def);

/**
 * Read string variable.
 *
 * @param name the name of the variable.
 * @param def a default value for the variable.
 *
 * @return the value if set or the default value if not set.
 */

string_t read_string_conf(string_t name, string_t def);


/**
 * Read int variable.
 *
 * @param name the name of the variable.
 * @param def a default value for the variable.
 *
 * @return the value if set or the default value if not set.
 */

int read_int_conf(string_t name, int def);

/**
 * Read data variable.
 *
 * @param name the name of the variable.
 * @param length set to the length of the data.
 * @param def a filename to read the data from.
 *
 * @return a pointer to the data or NULL on a failure.
 */

pointer_t read_data_conf(string_t name, int *length, string_t def);

END_C_DECL

#endif
