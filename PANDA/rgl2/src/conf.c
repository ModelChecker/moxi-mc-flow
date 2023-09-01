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


#include "conf.h"

#include <string.h>
#include <errno.h>

#define MAX_VARIABLES 1024
#define BUFFER_SIZE 4096

typedef enum 
  {
    CONSTANT_K, DOUBLE_K, STRING_K, INT_K, DATA_K
  } var_kind_t;

typedef struct 
{
  var_kind_t kind;
  string_t name;
  
  union 
  {
    double d;
    string_t s;
    int i;
    struct {
      pointer_t p;
      int len;
    } data;
  } val;
} var_t;

static int num_variables = 0;
static var_t variables[MAX_VARIABLES];


/** 
 * Reads in a configuration file.  Reads are additive and copy over.
 *
 * @param fp a file pointer to the file.
 *
 * @return the number of variables read or -1 on an error.
 */

int 
read_conf(FILE *fp)
{
  char buffer[BUFFER_SIZE];
  char name[BUFFER_SIZE];

  char string[BUFFER_SIZE];
  double real;
  int integer;
   
  int n = 0;
  
  char *temp;
  int len;

  int line = 0;

  while (1) 
    {
      char *result = fgets(buffer, BUFFER_SIZE, fp); 

      if (result == 0) return n;
      line ++;
      
      switch (result[0]) {
      case 'c':
	{
	  sscanf(buffer, "c %s\n", name);
	  len = strlen(name);

	  temp = (char *) malloc(sizeof(char) * (len+1) );

	  strcpy(temp, name);

	  variables[num_variables].kind = CONSTANT_K;
	  variables[num_variables].name = temp;

	  num_variables ++;
	  n ++;
	  
	  break;
	}
      case 'd':
	{
	  sscanf(buffer, "d %s %lf\n", name, &real);
	  len = strlen(name);

	  temp = (char *) malloc(sizeof(char) * (len+1));

	  strcpy(temp, name);

	  variables[num_variables].kind = DOUBLE_K;
	  variables[num_variables].name = temp;
	  variables[num_variables].val.d = real;
	 
	  num_variables ++;
	  n ++;

	  break;
	}
      case 's':
	{
	  sscanf(buffer, "s %s %s\n", name, string);
	  len = strlen(name);

	  temp = (char *) malloc(sizeof(char) * (len+1) );

	  strcpy(temp, name);

	  variables[num_variables].kind = STRING_K;
	  variables[num_variables].name = temp;

	  len = strlen(string);
	  
	  temp = (char *) malloc(sizeof(char) * (len+1));

	  strcpy(temp, string);

	  variables[num_variables].val.s = temp;

	  num_variables ++;
	  n ++;
	 
	  break;
	}
      case 'i':
	{
	  sscanf(buffer, "i %s %i\n", name, &integer);
	  len = strlen(name);

	  temp = (char *) malloc(sizeof(char) * (len+1));

	  strcpy(temp, name);
	  
	  variables[num_variables].kind = INT_K;
	  variables[num_variables].name = temp;
	  variables[num_variables].val.i = integer;

	  num_variables ++;
	  n ++;
	 
	  break;
	}
      case 'p':
	{
	  FILE *dfp;
	  pointer_t data;
	  
	  sscanf(buffer, "p %s %s\n", name, string);
	  len = strlen(name);

	  temp = (char *) malloc(sizeof(char) * (len+1));

	  strcpy(temp, name);

	  variables[num_variables].kind = DATA_K;
	  variables[num_variables].name = temp;
	  
	  dfp = fopen(string, "rb");
	  
	  if (dfp == NULL) {
	    char errs[1024];
	    
	    sprintf(errs, "error opening file %s\n", string);	    
	    perror(errs);

	    break;
	  }

	  if (fseek(dfp, 0, SEEK_END) != 0) {
	    char errs[1024];
	    
	    sprintf(errs, "error seeking end of file %s\n", string);	    
	    perror(errs);

	    break;
	  }
	  
	  len = ftell(dfp);
	  rewind(dfp);

	  data = malloc((size_t) len);

	  assert (data);

	  len = fread(data, sizeof(char), len, dfp);

	  variables[num_variables].val.data.p = data;
	  variables[num_variables].val.data.len = len;

	  num_variables ++;
	  n ++;

	  break;
	}
      case 'r':
	{
	  FILE *dfp;
	  int read;

	  sscanf(buffer, "c %s\n", name);

	  dfp = fopen(name, "r");

	  if (dfp == NULL) {
	    char errs[1024];
	    
	    sprintf(errs, "error opening file %s\n", name);	    
	    perror(errs);

	    break;
	  }	  
	  
	  read = read_conf(dfp);
	  
	  fclose(dfp);
	  
	  n += read;
	  
	  break;
	}
      case '#':
	{
	  break; // comment
	}
      default:
	{
	  if (result[0] != 0x0) fprintf(stderr, "read a '%c' in conf file on line %i - unknown code\n", result[0], line);
	  else fprintf(stderr, "read a NULL as first character on line %i in conf file\n", line);

	  break;
	}  // unknown code - drop the line
      }
    }

  return n;
}

/**
 * Writes a configuration file from the current state of the machine.
 *
 * @param fp a file pointer to the file.
 *
 * @return the number of variables written or -1 on an error.
 */

int 
write_conf(FILE *fp)
{
  int i;
  
  for (i=0; i<num_variables; i++) {
    switch (variables[i].kind) 
      {
      case CONSTANT_K:
	{
	  fprintf(fp, "c %s\n", variables[i].name);
	  break;
	}
      case INT_K:
	{
	  fprintf(fp, "i %s %i\n", variables[i].name, variables[i].val.i);
	  break;
	}
      case DOUBLE_K:
	{
	  fprintf(fp, "d %s %f\n", variables[i].name, variables[i].val.d);
	  break;
	}
      case STRING_K:
	{
	  fprintf(fp, "s %s %s\n", variables[i].name, variables[i].val.s);
	  break;
	}
      case DATA_K:
	{
	  FILE *dfp = fopen(variables[i].name, "wb");

	  if (dfp == NULL) {
	    char errs[1024];
	    
	    sprintf(errs, "error opening file %s\n", variables[i].name);	    
	    perror(errs);

	    break;
	  }	  
	  
	  fwrite(variables[i].val.data.p, variables[i].val.data.len, sizeof(char), dfp);
	  
	  fclose(dfp);
	  break;
	}
      default:
	{
	  assert ("garbage in variables data structure\n" == 0);
	  break;
	}
      }
  }

  return num_variables;
}

static int var_probe(string_t name)
{
    int i;

    for (i=0; i<num_variables; i++)    
	if ( strcmp( name, variables[i].name) == 0)
	    return i;
    
    return -1;  
}

/**
 * Checks if a variable is set.
 *
 * @param name the name of the variable.
 *
 * @return TRUE if the variable is set and false otherwise.
 */

boolean_t 
check_variable_conf(string_t name)
{
  if (var_probe(name) == -1) return FALSE;
  else return TRUE;
}

/**
 * Read double variable.
 *
 * @param name the name of the variable.
 * @param def a default value for the variable.
 *
 * @return the value if set or the default value if not set.
 */

double 
read_double_conf(string_t name, double def)
{
  int loc = var_probe(name);

  if (loc == -1) return def;
  
  assert (variables[loc].kind == DOUBLE_K);

  return variables[loc].val.d;
}


/**
 * Read string variable.
 *
 * @param name the name of the variable.
 * @param def a default value for the variable.
 *
 * @return the value if set or the default value if not set.
 */

string_t 
read_string_conf(string_t name, string_t def)
{
  int loc = var_probe(name);

  if (loc == -1) return def;
  
  assert (variables[loc].kind == STRING_K);

  return variables[loc].val.s;
}

/**
 * Read int variable.
 *
 * @param name the name of the variable.
 * @param def a default value for the variable.
 *
 * @return the value if set or the default value if not set.
 */

int 
read_int_conf(string_t name, int def)
{
  int loc = var_probe(name);
 
  if (loc == -1) return def;
  
  assert (variables[loc].kind == INT_K);

  return variables[loc].val.i;
}

/**
 * Read data variable.
 *
 * @param name the name of the variable.
 * @param length set to the length of the data.
 * @param def a filename to read the data from.
 *
 * @return a pointer to the data or NULL on a failure.
 */

pointer_t 
read_data_conf(string_t name, int *length, string_t def)
{
  int loc = var_probe(name);

  if (loc == -1) return NULL;
  
  assert (variables[loc].kind == DATA_K);

  *length = variables[loc].val.data.len;
  
  return variables[loc].val.data.p;
}
