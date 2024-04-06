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


#ifndef ___VECTOR_H__ABCDEEDCBA_
#define ___VECTOR_H__ABCDEEDCBA_

#include <stdio.h>
#include <stdlib.h>
#include <math.h>

#include "matrix.h"

//BEGIN_C_DECL

/** 
 *@defgroup GROUPVector Fast vector operations.
 */

/**
 * @ingroup GROUPVector
 * Defining vectors as pointers to  double.
 */
typedef double * vector_t;

/**
 *@ingroup GROUPVector
 *@brief Index where the dimension of the vector is stored.
 *
 * Index where the dimension of the vector is stored. 
 */
#define VECTOR_DIM_INDEX -1

/**
 *@ingroup GROUPVector
 *@brief Offset from the beginning of the pointer.
 *
 *Offset from the beginning of the pointer.
 */
#define VECTOR_ELEM_INDEX 1

/**
 *@ingroup GROUPMatrix
 *@brief Returns the first address of the pointer.
 *
 *Returns the first address of the pointer.
 *
 *@param v a pointer of type  vector_t to a vector of elements.
 */
#define get_address_vector(v)\
  (v - VECTOR_ELEM_INDEX)

/**
 *@ingroup GROUPVector
 *@brief Advances the vector pointer to the beginning of the elements.
 *
 *Advances  the vector pointer to the beginning of the elements.
 *
 *@param v a pointer of type  vector_t to a vector of elements.
 */
#define advance_vector(v)\
{\
  v = v + VECTOR_ELEM_INDEX;\
}

/**
 *@ingroup GROUPVector
 *@brief Accesses the dimension of the vector, i.e., number of elements.
 *
 *Accesses the dimension of the vector, i.e., number of elements.
 *
 *@param v a pointer of type  vector_t to a vector of elements.
 *
 *@return  number of elements
 */
#define get_dim_vector(v)\
((int) (v[VECTOR_DIM_INDEX]))

/**
 *@ingroup GROUPVector
 *@brief Accesses the i-th element.
 *
 *Accesses the i-th element.
 *
 *@param v a pointer of type  vector_t to a vector of elements.
 *@param i an integer in the range 0...DIM-1 representing the index.
 *
 *@returns the element at position i.
 */
#define get_elem_vector(v, i)\
(v[i])

/**
 *@ingroup GROUPVector
 *@brief Sets the i-th element to val, i.e., v[i] = val.
 *
 *Sets the i-th element to val, i.e., v[i] = val.
 *@param v a pointer of type  vector_t to a vector of elements.
 *@param i an integer in the range 0...DIM-1 representing the index.
 */
#define set_elem_vector(v, i, val)\
{\
    v[i] = val;\
}

/**
 *@ingroup GROUPVector
 *@brief Allocate memory.
 *
 *Allocate memory.
 *
 *@param v a pointer of type  vector_t to which no memory has been allocated.
 *@param t element type, i.e.,  double,  float,  int, etc.
 *@param d an integer representing the dimension of the vector.
 *
 *@descript allocates to v a contigous block of d elements of type t.
 */
#define alloc_vector(v,d,t)\
{\
    v = (t*)malloc(((d)+1)*sizeof(t));\
    advance_vector(v);\
    set_elem_vector(v, VECTOR_DIM_INDEX, d);\
}

/**
 *@ingroup GROUPVector
 *@brief Free memory.
 *
 *Free memory.
 *
 *@param v  a pointer of type  vector_t to a vector of elements.
 *
 *@descript frees the memory allocated to v.
 */
#define free_vector(v)\
{\
    if(v) {free(get_address_vector(v));}\
}

/**
 *@ingroup GROUPVector
 *@brief Reads vector elements from a file stream.
 *
 *Reads vector elements from a file stream.
 *
 *@param v  a pointer of type  vector_t to a vector of elements.
 *@param in a pointer to a file.
 *
 *@descript reads the elements of the vector v from the file to which in points to.
 */
#define read_vector(v,in)\
{\
    int dimVE000 = get_dim_vector(v);\
    int iVE000=0;\
    for(iVE000=0; iVE000<dimVE000; iVE000++ )\
       fscanf(in,"%lf",&(v[iVE000]));\
}

/**
 *@ingroup GROUPVector
 *@brief Prints vector elements to the standard output device.
 *
 *Prints vector elements to the standard output device.
 *
 *@param v  a pointer of type  vector_t to a vector of elements.
 */
#define print_vector(v)\
{\
    int dVE000   = get_dim_vector(v);\
    int iVE000=0;\
    printf("(%d):[", dVE000);\
    for (iVE000=0; iVE000<dVE000; iVE000++)\
	    printf("%f, ", v[iVE000]);\
    printf("]\n");\
}

/**
 *@ingroup GROUPVector
 *@brief Performs vector addition, i.e.,  v = v1 + v2.
 *
 *Performs vector addition, i.e.,  v = v1 + v2.
 *@param v  a pointer of type  vector_t to a vector of elements.
 *@param v1 a pointer of type  vector_t to a vector of elements.
 *@param v2 a pointer of type  vector_t to a vector of elements.
 */
#define add_vector(v1,v2,v)\
{\
    int dimVE000 = get_dim_vector(v);\
    int iVE000=0;\
    for(iVE000=0; iVE000<dimVE000; iVE000++)\
        v[iVE000] = v1[iVE000] + v2[iVE000];\
}

/**
 *@ingroup GROUPVector
 *@brief Performs vector subtraction, i.e., v = v1 - v2.
 *
 *Performs vector subtraction, i.e.,  v = v1 - v2.
 *
 *@param v  a pointer of type  vector_t to a vector of elements.
 *@param v1 a pointer of type  vector_t to a vector of elements.
 *@param v2 a pointer of type  vector_t to a vector of elements.
 */
#define sub_vector(v1,v2,v)\
{\
    int dimVE000 = get_dim_vector(v);\
    int iVE000=0;\
    for(iVE000=0; iVE000<dimVE000; iVE000++)\
        v[iVE000] = v1[iVE000] - v2[iVE000];\
}

/**
 *@ingroup GROUPVector
 *@brief Computes dot product of vectors.
 *
 *Computes dot product of vectors.
 *
 *@param v1 a pointer of type  vector_t to a vector of elements.
 *@param v2 a pointer of type  vector_t to a vector of elements.
 *@param d  a double variable where the result of the dot product is stored.
 */
#define dot_vector(v1,v2,d)\
{\
    int dimVE000 = get_dim_vector(v1);\
    int iVE000=0;\
    d = 0;\
    for(iVE000=0; iVE000 < dimVE000; iVE000++ )\
        d += (v1[iVE000] * v2[iVE000]);\
}

/**
 *@ingroup GROUPVector
 *@brief Multiplies a vector by a scalar.
 *
 *Multiplies a vector by a scalar.
 *
 *@param v1 a pointer of type  vector_t to a vector of elements.
 *@param d  a scalar value.
 *@param v  a pointer of type  vector_t to a vector of elements.
 */
#define multiply_scalar_vector(v1,d,v)\
{\
    int dimVE000 = get_dim_vector(v);\
    int iVE000=0;\
    for(iVE000=0; iVE000<dimVE000; iVE000++)\
        v[iVE000] = v1[iVE000]*(d);\
}


/**
 *@ingroup GROUPVector
 *@brief Multiplies a column vector with a row vector, i.e., m = v1 * v2. The result
 * is a matrix.
 *
 *Multiplies a column vector with a row vector, i.e., m = v1 * v2. The result
 *is a matrix.
 *
 *@param m  a pointer of type  matrix_t to a vector of elements.
 *@param v1 a pointer of type  vector_t to a vector of elements.
 *@param v2 a pointer of type  vector_t to a vector of elements.
 */
#define multiply_vector_vector(v1,v2,m)\
{\
    int dim1VE000 = get_dim_vector(v1);\
    int dim2VE000 = get_dim_vector(v2);\
    int cVE000    = get_cols_matrix(m);\
    int iVE000=0, jVE001=0;\
    for(iVE000=0; iVE000<dim1VE000; iVE000++ )\
        for(jVE001=0; jVE001<dim2VE000; jVE001++ )\
            m[iVE000*cVE000 + jVE001] = v1[iVE000] * v2[jVE001];\
}

/**
 *@ingroup GROUPVector
 *@brief Multiplies a row vector with a matrix, i.e., v = v1 * m. The result
 *is a row vector.
 *
 *Multiplies a row vector with a matrix, i.e., v = v1 * m. The result
 *is a row vector.
 *
 *@param v1 a pointer of type  vector_t to a vector of elements.
 *@param m  a pointer of type  matrix_t to a vector of elements.
 *@param v  a pointer of type  vector_t to a vector of elements.
 *
 *@warning If v1 and v point to the same vector of elements, then the result may be incorrect.
 */
#define multiply_vector_matrix(v1,m,v)\
{\
    int colsVE000 = get_cols_matrix(m);\
    int dim1VE000 = get_dim_vector(v1);\
    int iVE000=0, jVE001=0;\
    for(iVE000=0; iVE000<colsVE000; iVE000++ )\
    {\
        v[iVE000] = 0;\
        for(jVE001=0; jVE001<dim1VE000; jVE001++ )\
          v[iVE000] += (v1[jVE001] * m[jVE001*colsVE000 + iVE000]);\
    }\
}

/**
 *@ingroup GROUPVector
 *@brief Multiplies a  matrix with a column vector, i.e.,  v =  m *  v1. The result
 *is a column vector.
 *
 *Multiplies a  matrix with a column vector, i.e.,  v =  m *  v1. The result
 *is a column vector.
 *
 *@param m  a pointer of type  matrix_t to a vector of elements.
 *@param v1 a pointer of type  vector_t to a vector of elements.
 *@param v  a pointer of type  vector_t to a vector of elements.
 *
 *@warning If v1 and v point to the same vector of elements, then the result may be incorrect.
 */
#define multiply_matrix_vector(m,v1,v)\
{\
    int rowsVE000 = get_rows_matrix(m);\
    int colsVE000 = get_cols_matrix(m);\
    int dim1VE000 = get_dim_vector(v1);\
    int iVE000=0, jVE001=0;\
    for(iVE000=0; iVE000<rowsVE000; iVE000++ )\
    {\
	v[iVE000] = 0;\
	for(jVE001=0; jVE001<dim1VE000; jVE001++ )\
	   v[iVE000] += (v1[jVE001] * m[iVE000*colsVE000 + jVE001]);\
    }\
}

/**
 *@ingroup GROUPVector
 *@brief Linearly interpolates vectors v1 and v2, i.e., v = (1-f)*v1 + f * v2.
 *
 *Linearly interpolates vectors v1 and v2, i.e., v = (1-f)*v1 + f * v2.
 *
 *@param v1 a pointer of type  matrix_t to a vector of elements.
 *@param v2 a pointer of type  vector_t to a vector of elements.
 *@param f  a double representing the interpolation factor.
 *@param v  a pointer of type  vector_t to a vector of elements.
 */
#define interpolate_vector(v1,v2,f,v)\
{\
    int dimVE000 = get_dim_vector(v);\
    int iVE000=0;\
    for(iVE000=0; iVE000<dimVE000; iVE000++ )\
        v[iVE000] = (1.0 - f) * v1[iVE000] + f * v2[iVE000];\
}

/**
 *@ingroup GROUPVector
 *@brief Tests for vector equality.
 *
 *Tests for vector equality.
 *
 *@param v1 a pointer of type  vector_t to a vector of elements.
 *@param v2 a pointer of type  vector_t to a vector of elements.
 *@param b  a boolean variable.
 *
 *@descript sets  b to  TRUE iff every element of vector  v1 is equal to the
 * corresponding element in vector  v2.
 */
#define equal_vector(v1,v2,b)\
{\
    int dim1VE000 = get_dim_vector(v1);\
    int dim2VE000 = get_dim_vector(v2);\
     int iVE000=0;\
    b = dim1VE000 == dim2VE000;\
    for(iVE000=0; iVE000<dim1VE000 && b; iVE000++)\
       b = (v1[iVE000] == v2[iVE000]);\
}

/**
 *@ingroup GROUPVector
 *@brief Copies vector v1 into vector v, i.e., v =  COPY(v1).
 *
 *Copies vector v1 into vector v, i.e., v =  COPY(v1).
 *
 *@param v  a pointer of type  vector_t to a vector of elements.
 *@param v1 a pointer of type  vector_t to a vector of elements.
 */
#define copy_vector(v,v1)\
{\
    int dimVE000 = get_dim_vector(v);\
     int iVE000=0;\
    for(iVE000=0; iVE000<dimVE000; iVE000++)\
        v[iVE000] = v1[iVE000];\
}

/**
 *@ingroup GROUPVector
 *@brief Computes the magnitude of the difference vector, i.e., d = MAG(v1 - v2).
 *
 *Computes the magnitude of the difference vector, i.e., d = MAG(v1 - v2).
 *
 *@param v1 a pointer of type  vector_t to a vector of elements.
 *@param v2 a pointer of type  vector_t to a vector of elements.
 *@param d  a double where the result is stored.
 */
#define distance_vector(v1,v2,d)\
{\
    int dimVE000 = get_dim_vector(v1);\
     int iVE000=0;\
    d = 0;\
    for(iVE000=0; iVE000<dimVE000; iVE000++ )\
        d += (v1[iVE000]-v2[iVE000])*(v1[iVE000]-v2[iVE000]);\
    d = sqrt(d);\
}
/**
 *@ingroup GROUPVector
 *@brief Computes the dot product of the difference vector with itself, i.e., d = (v1 - v2) * (v1 - v2).
 *
 *Computes the dot product of the difference vector with itself, i.e., d = (v1 - v2) * (v1 - v2).
 *
 *@param v1 a pointer of type  vector_t to a vector of elements.
 *@param v2 a pointer of type  vector_t to a vector of elements.
 *@param d  a double where the result is stored.
 */
#define squared_distance_vector(v1,v2,d)\
{\
    int dimVE000 = get_dim_vector(v1);\
    int iVE000=0;\
    d = 0;\
    for(iVE000=0; iVE000<dimVE000; iVE000++ )\
        d += (v1[iVE000]-v2[iVE000])*(v1[iVE000]-v2[iVE000]);\
}

/**
 *@ingroup GROUPVector
 *@brief Computes the magnitude of the vector.
 *
 *Computes the magnitude of the vector.
 *
 *@param v  a pointer of type  vector_t to a vector of elements.
 *@param d  a double where the magnitude is stored.
 */
#define magnitude_vector(v,d)\
{\
     dot_vector(v, v, d);\
     d = sqrt(d);\
}

/**
 *@ingroup GROUPVector
 *@brief Normalizes the vector.
 *
 *Normalizes the vector.
 *
 *@param v  a pointer of type  vector_t to a vector of elements.
 */
#define make_unit_vector(v)\
{\
    double magVE000;\
    magnitude_vector(v,magVE000);\
    if (magVE000!=0)\
    {\
	magVE000 = 1.0 / magVE000;\
        multiply_scalar_vector(v, magVE000, v);\
    }\
}
/**
 *@ingroup GROUPVector
 *@brief Sets every element of vector v to 0.
 *
 *Sets every element of vector v to 0.
 *
 *@param v a pointer of type  vector_t to a vector of elements.
 */
#define zero_vector(v)\
{\
    int dimVE000 = get_dim_vector(m);\
     int iVE000=0;\
    for(iVE000=0; iVE000<dimVE000; iVE000++)\
        v[iVE000] = 0;\
}

//END_C_DECL

#endif
