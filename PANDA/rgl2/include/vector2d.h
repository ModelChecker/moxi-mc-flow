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


#ifndef ___VECTOR2D_H__ABCDEEDCBA_
#define ___VECTOR2D_H__ABCDEEDCBA_

#include <stdio.h>
#include <stdlib.h>
#include <math.h>

//BEGIN_C_DECL

/** 
 *@defgroup GROUPVector2d Fast 2d vector operations.
 */

/**
 * @ingroup GROUPVector2d
 * Defining 2d vectors as pointers to double.
 */
typedef double * vector2d_t;

/**
 *@ingroup GROUPVector2d
 *@brief Accesses the i-th element.
 *
 *Accesses the i-th element.
 *
 *@param v a pointer of type  vector2d_t to a vector of 2 elements.
 *@param i an integer in the range 0...DIM-1 representing the index.
 *
 *@returns the element at position i.
 */
#define get_elem_vector2d(v, i)\
(v[i])

/**
 *@ingroup GROUPVector2d
 *@brief Sets the i-th element to val, i.e., v[i] = val.
 *
 *Sets the i-th element to val, i.e., v[i] = val.
 *
 *@param v a pointer of type  vector2d_t to a vector of 2 elements.
 *@param i an integer in the range 0...DIM-1 representing the index.
 */
#define set_elem_vector2d(v, i, val)\
{\
    v[i] = val;\
}

/**
 *@ingroup GROUPVector2d
 *@brief Allocate memory.
 *
 *Allocate memory.
 *
 *@param v a pointer of type  vector2d_t to which no memory has been allocated.
 *@param t element type, i.e.,  double,  float,  int, etc.
 *
 *@descript allocates to  v  a contigous block of 3 elements of type  t.
 */
#define alloc_vector2d(v,t)\
{\
    v = (t*)malloc(2*sizeof(t));\
}

/**
 *@ingroup GROUPVector2d
 *@brief Free memory.
 *
 *Free memory.
 *
 *@param v  a pointer of type  vector2d_t to a vector of 2 elements.
 *
 *@descript frees the memory allocated to v.
 */
#define free_vector2d(v)\
{\
    if(v) {free(v); v = NULL;}\
}


/**
 *@ingroup GROUPVector2d
 *@brief Reads vector elements from a file stream.
 *
 *Reads vector elements from a file stream.
 *
 *@param v  a pointer of type  vector2d_t to a vector of 2 elements.
 *@param in a pointer to a file.
 */
#define read_vector2d(v,in)\
{\
    fscanf(in,"%lf %lf %lf",&(v[0]),&(v[1]));\
}

/**
 *@ingroup GROUPVector2d
 *@brief Prints vector elements to the output stream.
 *
 *Prints vector elements to the output stream.
 *
 *@param v   a pointer of type  vector2d_t to a vector of 2 elements.
 *@param out a pointer to a file.
 */
#define print_vector2d(v, out)\
{\
    fprintf(out, "[%f, %f]", v[0], v[1]);\
}

/**
 *@ingroup GROUPVector2d
 *@brief Sets the vector elements.
 *
 *Sets the vector elements.
 *
 *@param a  a variable of the same or compatible type with vector elements.
 *@param b  a variable of the same or compatible type with vector elements.
 *@param v  a pointer of type  vector2d_t to a vector of 2 elements.
 */
#define set_vector2d(a,b,v)\
{\
    v[0] = a;\
    v[1] = b;\
}

/**
 *@ingroup GROUPVector2d
 *@brief Performs vector addition, i.e.,  v = v1 + v2.
 *
 *Performs vector addition, i.e.,  v = v1 + v2.
 *
 *@param v1 a pointer of type  vector2d_t to a vector of 2 elements.
 *@param v2 a pointer of type  vector2d_t to a vector of 2 elements.
 *@param v  a pointer of type  vector2d_t to a vector of 2 elements.
 */
#define add_vector2d(v1,v2,v)\
{\
    v[0] = v1[0] + v2[0];\
    v[1] = v1[1] + v2[1];\
}

/**
 *@ingroup GROUPVector2d
 *@brief Performs vector subtraction, i.e., v = v1 - v2.
 *
 *Performs vector subtraction, i.e.,  v = v1 - v2.
 *@param v1 a pointer of type  vector2d_t to a vector of 2 elements.
 *@param v2 a pointer of type  vector2d_t to a vector of 2 elements.
 *@param v  a pointer of type  vector2d_t to a vector of 2 elements.
 */
#define sub_vector2d(v1,v2,v)\
{\
    v[0] = v1[0] - v2[0];\
    v[1] = v1[1] - v2[1];\
}

/**
 *@ingroup GROUPVector2d
 *@brief Computes dot product of vectors.
 *
 *Computes dot product of vectors.
 *
 *@param v1 a pointer of type  vector2d_t to a vector of 2 elements.
 *@param v2 a pointer of type  vector2d_t to a vector of 2 elements.
 *@param d  a double variable where the result of the dot product is stored.
 */
#define dot_vector2d(v1,v2,d)\
{\
    d = v1[0] * v2[0] + v1[1] * v2[1];\
}

/**
 *@ingroup GROUPVector2d
 *@brief Multiplies a vector by a scalar.
 *
 *Multiplies a vector by a scalar.
 *
 *@param v1 a pointer of type  vector2d_t to a vector of 2 elements.
 *@param d  a scalar value.
 *@param v  a pointer of type  vector2d_t to a vector of 2 elements.
 */
#define multiply_scalar_vector2d(v1,d,v)\
{\
    v[0] = v1[0] * d;\
    v[1] = v1[1] * d;\
}
/**
 *@ingroup GROUPVector2d
 *@brief Multiplies a column vector with a row vector, i.e., m = v1 * v2. The result
 * is a matrix.
 *
 *Multiplies a column vector with a row vector, i.e., m = v1 * v2. The result
 *is a matrix.
 *
 *@param m  a pointer of type  matrix2by2_t to a vector of  4 elements.
 *@param v1 a pointer of type  vector2d_t to a vector of 2 elements.
 *@param v2 a pointer of type  vector2d_t to a vector of 2 elements.
 */
#define multiply_vector_vector2d(v1,v2,m)\
{\
    m[0] = v1[0]*v2[0];     m[1] = v1[0]*v2[1];\    
    m[2] = v1[1]*v2[0];     m[3] = v1[1]*v2[1];\
}

/**
 *@ingroup GROUPVector2d
 *@brief Multiplies a row vector with a matrix, i.e., v = v1 * m. The result
 *is a row vector.
 *
 *Multiplies a row vector with a matrix, i.e., v = v1 * m. The result
 *is a row vector.
 *
 *@param v1 a pointer of type  vector2d_t to a vector of 2 elements.
 *@param m  a pointer of type  matrix2by2_t to a vector of 4 elements.
 *@param v  a pointer of type  vector2d_t to a vector of 2 elements.
 *
 *@warning If v points to the same vector as v1, the result may be incorrect.
 */
#define multiply_vector_matrix2d(v1,m,v)\
{\
    v[0] = v1[0] * m[0] + v1[1] * m[2];\
	v[1] = v1[0] * m[1] + v1[1] * m[3];\
}


/**
 *@ingroup GROUPVector2d
 *@brief Multiplies a  matrix with a column vector, i.e.,  v =  m *  v1. The result
 *is a column vector.
 *
 *Multiplies a  matrix with a column vector, i.e.,  v =  m *  v1. The result
 *is a column vector.
 *
 *@param m  a pointer of type  matrix2by2_t to a vector of 4 elements.
 *@param v1 a pointer of type  vector2d_t to a vector of 2 elements.
 *@param v  a pointer of type  vector2d_t to a vector of 2 elements.
 *
 *@warning If v points to the same vector as v1, the result may be incorrect
 */
#define multiply_matrix_vector2d(m,v1,v)\
{\
    v[0] = m[0] * v1[0] + m[1] * v1[1];\
	v[1] = m[2] * v1[0] + m[3] * v1[1];\
}

/**
 *@ingroup GROUPVector2d
 *@brief Linearly interpolates vectors v1 and v2, i.e., v = (1-f)*v1 + f * v2.
 *
 *Linearly interpolates vectors v1 and v2, i.e., v = (1-f)*v1 + f * v2.
 *
 *@param v1 a pointer of type  vector2d_t to a vector of 2 elements.
 *@param v2 a pointer of type  vector2d_t to a vector of 2 elements.
 *@param f  a double representing the interpolation factor.
 *@param v  a pointer of type  vector2d_t to a vector of 2 elements.
 */
#define interpolate_vector2d(v1,v2,f,v)\
{\
    v[0] = (1.0 - f) * v1[0] + f * v2[0];\
    v[1] = (1.0 - f) * v1[1] + f * v2[1];\
}

/**
 *@ingroup GROUPVector2d
 *@brief Tests for vector equality.
 *
 *Tests for vector equality.
 *
 *@param v1 a pointer of type  vector2d_t to a vector of 2 elements.
 *@param v2 a pointer of type  vector2d_t to a vector of 2 elements.
 *@param b  a boolean variable.
 *
 *@descript sets  b to  TRUE iff every element of vector  v1 is equal to the
 * corresponding element in vector  v2.
 */
#define equal_vector2d(v1,v2,b)\
{\
    b = (v1[0] == v2[0] && v1[1] == v2[1]);\
}

/**
 *@ingroup GROUPVector2d
 *@brief Copies vector v1 into vector v, i.e., v =  COPY(v1).
 *
 *Copies vector v1 into vector v, i.e., v =  COPY(v1).
 *
 *@param v  a pointer of type  vector2d_t to a vector of 2 elements.
 *@param v1 a pointer of type  vector2d_t to a vector of 2 elements.
 */
#define copy_vector2d(v,v1)\
{\
    v[0] = v1[0];\
    v[1] = v1[1];\
}

/**
 *@ingroup GROUPVector2d
 *@brief Computes the magnitude of the difference vector, i.e., d = MAG(v1 - v2).
 *
 *Computes the magnitude of the difference vector, i.e., d = MAG(v1 - v2).
 *
 *@param v1 a pointer of type  vector2d_t to a vector of 2 elements.
 *@param v2 a pointer of type  vector2d_t to a vector of 2 elements.
 *@param d  a double where the result is stored.
 */
#define distance_vector2d(v1,v2,d)\
{\
    d = sqrt( (v1[0]-v2[0])*(v1[0]-v2[0]) + (v1[1]-v2[1])*(v1[1]-v2[1]));\
}

/**
 *@ingroup GROUPVector2d
 *@brief Computes the dot product of the difference vector with itself, i.e., d = (v1 - v2) * (v1 - v2).
 *
 *Computes the dot product of the difference vector with itself, i.e., d = (v1 - v2) * (v1 - v2).
 *
 *@param v1 a pointer of type  vector2d_t to a vector of 2 elements.
 *@param v2 a pointer of type  vector2d_t to a vector of 2 elements.
 *@param d  a double where the result is stored.
 */
#define squared_distance_vector2d(v1,v2,d)\
{\
    d = (v1[0]-v2[0])*(v1[0]-v2[0]) + (v1[1]-v2[1])*(v1[1]-v2[1]));\
}

/**
 *@ingroup GROUPVector2d
 *@brief Computes the magnitude of the vector.
 *
 *Computes the magnitude of the vector.
 *
 *@param v  a pointer of type  vector2d_t to a vector of 2 elements.
 *@param d  a double where the magnitude is stored.
 */
#define magnitude_vector2d(v,d)\
{\
    d = sqrt( v[0]*v[0] + v[1]*v[1]);\
}

/**
 *@ingroup GROUPVector2d
 *@brief Normalizes the vector.
 *
 *Normalizes the vector.
 *
 *@param v  a pointer of type  vector2d_t to a vector of 2 elements.
 */   
#define make_unit_vector2d(v)\
{\
    double magV2000;\
    magnitude_vector2d(v,magV2000);\
    if (magV2000!=0)\
    {\
        v[0] = v[0] / magV2000;\
        v[1] = v[1] / magV2000;\
    }\
}

/**
 *@ingroup GROUPVector2d
 *@brief Sets every element of vector v to 0.
 *
 *Sets every element of vector v to 0.
 *
 *@param v a pointer of type  vector2d_t to a vector of 2 elements.
 */
#define zero_vector2d(v)\
{\
   v[0] = v[1] = 0;\
}

//END_C_DECL

#endif
