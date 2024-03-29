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


#ifndef ___VECTOR3D_H__ABCDEEDCBA_
#define ___VECTOR3D_H__ABCDEEDCBA_

#include <stdio.h>
#include <stdlib.h>
#include <math.h>

BEGIN_C_DECL

/** 
 *@defgroup GROUPVector3d Fast 3d vector operations.
 */

/**
 * @ingroup GROUPVector3d
 * Defining 3d vectors as pointers to double.
 */
typedef double * vector3d_t;

/**
 *@ingroup GROUPVector3d
 *@brief Accesses the i-th element.
 *
 *Accesses the i-th element.
 *
 *@param v a pointer of type  vector3d_t to a vector of 3 elements.
 *@param i an integer in the range 0...DIM-1 representing the index.
 *
 *@returns the element at position i.
 */
#define get_elem_vector3d(v, i)\
(v[i])

/**
 *@ingroup GROUPVector3d
 *@brief Sets the i-th element to val, i.e., v[i] = val.
 *
 *Sets the i-th element to val, i.e., v[i] = val.
 *
 *@param v a pointer of type  vector3d_t to a vector of 3 elements.
 *@param i an integer in the range 0...DIM-1 representing the index.
 */
#define set_elem_vector3d(v, i, val)\
{\
    v[i] = val;\
}

/**
 *@ingroup GROUPVector3d
 *@brief Allocate memory.
 *
 *Allocate memory.
 *
 *@param v a pointer of type  vector3d_t to which no memory has been allocated.
 *@param t element type, i.e.,  double,  float,  int, etc.
 *
 *@descript allocates to  v  a contigous block of 9 elements of type  t.
 */
#define alloc_vector3d(v,t)\
{\
    v = (t*)malloc(3*sizeof(t));\
}

/**
 *@ingroup GROUPVector3d
 *@brief Free memory.
 *
 *Free memory.
 *
 *@param v  a pointer of type  vector3d_t to a vector of 3 elements.
 *
 *@descript frees the memory allocated to v.
 */
#define free_vector3d(v)\
{\
    if(v) {free(v); v = NULL;}\
}


/**
 *@ingroup GROUPVector3d
 *@brief Reads vector elements from a file stream.
 *
 *Reads vector elements from a file stream.
 *
 *@param v  a pointer of type  vector3d_t to a vector of 3 elements.
 *@param in a pointer to a file.
 *
 *@descript reads the elements of the vector v from the file to which in points to.
 */
#define read_vector3d(v,in)\
{\
    fscanf(in,"%lf %lf %lf",&(v[0]),&(v[1]),&(v[2]));\
}

/**
 *@ingroup GROUPVector3d
 *@brief Prints vector elements to the standard output device.
 *
 *Prints vector elements to the standard output device.
 *
 *@param v  a pointer of type  vector3d_t to a vector of 3 elements.
 */
#define print_vector3d(v)\
{\
    printf("[%f, %f, %f]", v[0], v[1], v[2] );\
}

/**
 *@ingroup GROUPVector3d
 *@brief Sets the vector elements.
 *
 *Sets the vector elements.
 *
 *@param a  a variable of the same or compatible type with vector elements.
 *@param b  a variable of the same or compatible type with vector elements.
 *@param c  a variable of the same or compatible type with vector elements.
 *@param v  a pointer of type  vector3d_t to a vector of 3 elements.
 */
#define set_vector3d(a,b,c,v)\
{\
    v[0] = a;\
    v[1] = b;\
    v[2] = c;\
}

/**
 *@ingroup GROUPVector3d
 *@brief Performs vector addition, i.e.,  v = v1 + v2.
 *
 *Performs vector addition, i.e.,  v = v1 + v2.
 *
 *@param v1 a pointer of type  vector3d_t to a vector of 3 elements.
 *@param v2 a pointer of type  vector3d_t to a vector of 3 elements.
 *@param v  a pointer of type  vector3d_t to a vector of 3 elements.
 */
#define add_vector3d(v1,v2,v)\
{\
    v[0] = v1[0] + v2[0];\
    v[1] = v1[1] + v2[1];\
    v[2] = v1[2] + v2[2];\
}

/**
 *@ingroup GROUPVector3d
 *@brief Performs vector subtraction, i.e., v = v1 - v2.
 *
 *Performs vector subtraction, i.e.,  v = v1 - v2.
 *@param v1 a pointer of type  vector3d_t to a vector of 3 elements.
 *@param v2 a pointer of type  vector3d_t to a vector of 3 elements.
 *@param v  a pointer of type  vector3d_t to a vector of 3 elements.
 */
#define sub_vector3d(v1,v2,v)\
{\
    v[0] = v1[0] - v2[0];\
    v[1] = v1[1] - v2[1];\
    v[2] = v1[2] - v2[2];\
}

/**
 *@ingroup GROUPVector3d
 *@brief Computes cross product of vectors.
 *
 *Computes cross product of vectors.
 *
 *@param v1 a pointer of type  vector3d_t to a vector of 3 elements.
 *@param v2 a pointer of type  vector3d_t to a vector of 3 elements.
 *@param v  a pointer of type  vector3d_t to a vector of 3 elements
 *
 *@warning If v points to the same vector as either v1 or v2, the result may be incorrect.
 */
#define cross_vector3d(v1,v2,v)\
{\
   v[0] = v1[1] * v2[2] - v1[2] * v2[1];\
   v[1] = v1[0] * v2[2] - v1[2] * v2[0];\
   v[2] = v1[0] * v2[1] - v1[1] * v2[0];\
}

/**
 *@ingroup GROUPVector3d
 *@brief Computes dot product of vectors.
 *
 *Computes dot product of vectors.
 *
 *@param v1 a pointer of type  vector3d_t to a vector of 3 elements.
 *@param v2 a pointer of type  vector3d_t to a vector of 3 elements.
 *@param d  a double variable where the result of the dot product is stored.
 */
#define dot_vector3d(v1,v2,d)\
{\
    d = v1[0] * v2[0] + v1[1] * v2[1] + v1[2] * v2[2];\
}

/**
 *@ingroup GROUPVector3d
 *@brief Multiplies a vector by a scalar.
 *
 *Multiplies a vector by a scalar.
 *
 *@param v1 a pointer of type  vector3d_t to a vector of 3 elements.
 *@param d  a scalar value.
 *@param v  a pointer of type  vector3d_t to a vector of 3 elements.
 *
 *@descript multiplies each element of vector v1 by the scalar d and stores the result 
 *in the corresponding element of vector  v.
 */
#define multiply_scalar_vector3d(v1,d,v)\
{\
    v[0] = v1[0] * d;\
    v[1] = v1[1] * d;\
    v[2] = v1[2] * d;\
}
/**
 *@ingroup GROUPVector3d
 *@brief Multiplies a column vector with a row vector, i.e., m = v1 * v2. The result
 * is a matrix.
 *
 *Multiplies a column vector with a row vector, i.e., m = v1 * v2. The result
 *is a matrix.
 *
 *@param m  a pointer of type  matrix_t to a vector of 3 elements.
 *@param v1 a pointer of type  vector3d_t to a vector of 3 elements.
 *@param v2 a pointer of type  vector3d_t to a vector of 3 elements.
 */
#define multiply_vector_vector3d(v1,v2,m)\
{\
    m[0] = v1[0]*v2[0];     m[1] = v1[0]*v2[1];    m[2] = v1[0]*v2[2];\
    m[3] = v1[1]*v2[0];     m[4] = v1[1]*v2[1];    m[5] = v1[1]*v2[2];\
    m[6] = v1[2]*v2[0];     m[7] = v1[2]*v2[1];    m[8] = v1[2]*v2[2];\
}

/**
 *@ingroup GROUPVector3d
 *@brief Multiplies a row vector with a matrix, i.e., v = v1 * m. The result
 *is a row vector.
 *
 *Multiplies a row vector with a matrix, i.e., v = v1 * m. The result
 *is a row vector.
 *
 *@param v1 a pointer of type  vector3d_t to a vector of 3 elements.
 *@param m  a pointer of type  matrix_t to a vector of 3 elements.
 *@param v  a pointer of type  vector3d_t to a vector of 3 elements.
 *
 *@warning If v points to the same vector as v1, the result may be incorrect.
 */
#define multiply_vector_matrix3d(v1,m,v)\
{\
    v[0] = v1[0] * m[0] + v1[1] * m[3] + v1[2] * m[6];\
    v[1] = v1[0] * m[1] + v1[1] * m[4] + v1[2] * m[7];\
    v[2] = v1[0] * m[2] + v1[1] * m[5] + v1[2] * m[8];\
}


/**
 *@ingroup GROUPVector3d
 *@brief Multiplies a  matrix with a column vector, i.e.,  v =  m *  v1. The result
 *is a column vector.
 *
 *Multiplies a  matrix with a column vector, i.e.,  v =  m *  v1. The result
 *is a column vector.
 *
 *@param m  a pointer of type  matrix_t to a vector of 3 elements.
 *@param v1 a pointer of type  vector3d_t to a vector of 3 elements.
 *@param v  a pointer of type  vector3d_t to a vector of 3 elements.
 *
 *@warning If v points to the same vector as v1, the result may be incorrect
 */
#define multiply_matrix_vector3d(m,v1,v)\
{\
    v[0] = v1[0] * m[0] + v1[1] * m[1] + v1[2] * m[2];\
    v[1] = v1[0] * m[3] + v1[1] * m[4] + v1[2] * m[5];\
    v[2] = v1[0] * m[6] + v1[1] * m[7] + v1[2] * m[8];\
}

/**
 *@ingroup GROUPVector3d
 *@brief Multiplies a  vector with a quaternion, i.e.,  v =  v1 *  o. The result
 *is a vector.
 *
 *Multiplies a  vector with a quaternion, i.e.,  v =  v1 *  o. The result
 *is a vector.
 *
 *@param v1 a pointer of type  vector3d_t to a vector of 3 elements.
 *@param o  a pointer of type  quaternion_t.
 *@param v  a pointer of type  vector3d_t to a vector of 3 elements.
 *
 *@warning If v points to the same vector as v1, the result may be incorrect
 */

#define multiply_vector_quaternion3d(v1,o,v)\
{\
    v[0] = v1[0] * (1 - 2*o[1]*o[1] - 2*o[2]*o[2]) + v1[1] * (2*o[0]*o[1] - 2*o[2]*o[3])     + v1[2] * (2*o[0]*o[2] + 2*o[1]*o[3]);\
    v[1] = v1[0] * (2*o[0]*o[1] + 2*o[2]*o[3])     + v1[1] * (1 - 2*o[0]*o[0] - 2*o[2]*o[2]) + v1[2] * (2*o[1]*o[2] - 2*o[0]*o[3]);\
    v[2] = v1[0] * (2*o[0]*o[2] - 2*o[1]*o[3])     + v1[1] * (2*o[1]*o[2] + 2*o[0]*o[3])     + v1[2] * (1 - 2*o[0]*o[0] - 2*o[1]*o[1]);\
}


/**
 *@ingroup GROUPVector3d
 *@brief Linearly interpolates vectors v1 and v2, i.e., v = (1-f)*v1 + f * v2.
 *
 *Linearly interpolates vectors v1 and v2, i.e., v = (1-f)*v1 + f * v2.
 *
 *@param v1 a pointer of type  vector3d_t to a vector of 3 elements.
 *@param v2 a pointer of type  vector3d_t to a vector of 3 elements.
 *@param f  a double representing the interpolation factor.
 *@param v  a pointer of type  vector3d_t to a vector of 3 elements.
 */
#define interpolate_vector3d(v1,v2,f,v)\
{\
    v[0] = (1.0 - f) * v1[0] + f * v2[0];\
    v[1] = (1.0 - f) * v1[1] + f * v2[1];\
    v[2] = (1.0 - f) * v1[2] + f * v2[2];\
}

/**
 *@ingroup GROUPVector3d
 *@brief Tests for vector equality.
 *
 *Tests for vector equality.
 *
 *@param v1 a pointer of type  vector3d_t to a vector of 3 elements.
 *@param v2 a pointer of type  vector3d_t to a vector of 3 elements.
 *@param b  a boolean variable.
 *
 *@descript sets  b to  TRUE iff every element of vector  v1 is equal to the
 * corresponding element in vector  v2.
 */
#define equal_vector3d(v1,v2,b)\
{\
    b = (v1[0] == v2[0] && v1[1] == v2[1] && v1[2] == v2[2] );\
}

/**
 *@ingroup GROUPVector3d
 *@brief Copies vector v1 into vector v, i.e., v =  COPY(v1).
 *
 *Copies vector v1 into vector v, i.e., v =  COPY(v1).
 *
 *@param v  a pointer of type  vector3d_t to a vector of 3 elements.
 *@param v1 a pointer of type  vector3d_t to a vector of 3 elements.
 */
#define copy_vector3d(v,v1)\
{\
    v[0] = v1[0];\
    v[1] = v1[1];\
    v[2] = v1[2];\
}

/**
 *@ingroup GROUPVector3d
 *@brief Computes the magnitude of the difference vector, i.e., d = MAG(v1 - v2).
 *
 *Computes the magnitude of the difference vector, i.e., d = MAG(v1 - v2).
 *
 *@param v1 a pointer of type  vector3d_t to a vector of 3 elements.
 *@param v2 a pointer of type  vector3d_t to a vector of 3 elements.
 *@param d  a double where the result is stored.
 */
#define distance_vector3d(v1,v2,d)\
{\
    d = sqrt( (v1[0]-v2[0])*(v1[0]-v2[0]) + (v1[1]-v2[1])*(v1[1]-v2[1]) + (v1[2]-v2[2])*(v1[2]-v2[2]) );\
}

/**
 *@ingroup GROUPVector3d
 *@brief Computes the dot product of the difference vector with itself, i.e., d = (v1 - v2) * (v1 - v2).
 *
 *Computes the dot product of the difference vector with itself, i.e., d = (v1 - v2) * (v1 - v2).
 *
 *@param v1 a pointer of type  vector3d_t to a vector of 3 elements.
 *@param v2 a pointer of type  vector3d_t to a vector of 3 elements.
 *@param d  a double where the result is stored.
 */
#define squared_distance_vector3d(v1,v2,d)\
{\
    d = (v1[0]-v2[0])*(v1[0]-v2[0]) + (v1[1]-v2[1])*(v1[1]-v2[1]) + (v1[2]-v2[2])*(v1[2]-v2[2]);\
}

/**
 *@ingroup GROUPVector3d
 *@brief Computes the magnitude of the vector.
 *
 *Computes the magnitude of the vector.
 *
 *@param v  a pointer of type  vector3d_t to a vector of 3 elements.
 *@param d  a double where the magnitude is stored.
 */
#define magnitude_vector3d(v,d)\
{\
    d = sqrt( v[0]*v[0] + v[1]*v[1] + v[2]*v[2] );\
}

/**
 *@ingroup GROUPVector3d
 *@brief Normalizes the vector.
 *
 *Normalizes the vector.
 *
 *@param v  a pointer of type  vector3d_t to a vector of 3 elements.
 */   
#define make_unit_vector3d(v)\
{\
    double magV3000;\
    magnitude_vector3d(v,magV3000);\
    if (magV3000!=0)\
    {\
        v[0] = v[0] / magV3000;\
        v[1] = v[1] / magV3000;\
        v[2] = v[2] / magV3000;\
    }\
}

/**
 *@ingroup GROUPVector3d
 *@brief Sets every element of vector v to 0.
 *
 *Sets every element of vector v to 0.
 *
 *@param v a pointer of type  vector3d_t to a vector of 3 elements.
 */
#define zero_vector3d(v)\
{\
   v[0] = v[1] = v[2] = 0;\
}

END_C_DECL

#endif
