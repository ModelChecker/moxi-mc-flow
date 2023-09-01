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


#ifndef ___MATRIX4BY4_H__ABCDEEDCBA_
#define ___MATRIX4BY4_H__ABCDEEDCBA_

#include <stdio.h>
#include <stdlib.h>
#include <math.h>

//BEGIN_C_DECL

/** 
 *@defgroup GROUPMatrix4by4 Fast 4x4 matrix operations.
 */

/**
 * @ingroup GROUPMatrix4by4
 * Defining 4x4 matrices as pointers to  double.
 */
typedef double * matrix4by4_t;

/**
 *@ingroup GROUPMatrix4by4
 *@brief Access matrix element, i.e., m[r][c].
 *
 *Access matrix element. i.e.,   m[r][c] .
 *
 *@param m a pointer of type  matrix4by4_t to a 16 element vector.
 *@param r an integer in the range 0...3 representing row index.
 *@param c an integer in the range 0...3 representing column index.
 *
 *@returns the element in row  r and column  c of matrix  m.
 */
#define get_elem_matrix4by4(m, r, c)\
(m[(r)*4 + (c)])

/**
 *@ingroup GROUPMatrix4by4
 *@brief Set matrix element, i.e., m[r][c] = v.
 *
 *Set matrix element, i.e.,  m[r][c] = v .
 *
 *@param m  a pointer of type  matrix4by4_t to a 16 element vector.
 *@param r an integer in the range 0...3 representing row index.
 *@param c an integer in the range 0...3 representing column index.
 *@param v a double.
 * 
 *@descript sets the value of the element in row  r and column  c of matrix  m  to  v.
 */
#define set_elem_matrix4by4(m, r, c, v)\
{\
    m[(r)*4 + (c)] = v;\
}

/**
 *@ingroup GROUPMatrix4by4
 *@brief Allocate memory.
 *
 *Allocate memory.
 *
 *@param m a pointer of type  matrix4by4_t to which no memory has been allocated.
 *@param t element type, i.e.,  double,  float,  int, etc.
 *
 *@descript allocates to  m  a contigous block of 16 elements of type  t.
 */
#define alloc_matrix4by4(m,t)\
{\
    m = (t*)malloc(16*sizeof(t));\
}

/**
 *@ingroup GROUPMatrix4by4
 *@brief Free memory.
 *
 *Free memory.
 *
 *@param m  a pointer of type  matrix4by4_t to a 16 element vector.
 *
 *@descript frees the memory allocated to  m.
 */
#define free_matrix4by4(m)\
{\
    if(m) {free(m); m = NULL;}\
}

/**
 *@ingroup GROUPMatrix4by4
 *@brief Reads matrix elements from a file stream.
 *
 *Reads matrix elements from a file stream.
 *
 *@param m  a pointer of type  matrix4by4_t to a 16 element vector.
 *@param in a pointer to a file.
 *
 *@descript reads the 16 elements of matrix  m from the file to which  in points to.
 */
#define read_matrix4by4(m,in)\
{\
    fscanf( in, "%lf %lf %lf %lf %lf %lf %lf %lf %lf %lf %lf %lf %lf %lf %lf %lf",\
    &(m[0]),&(m[1]),&(m[2]),&(m[3]),&(m[4]),&(m[5]),&(m[6]),&(m[7]),&(m[8]),&(m[9]),\
    &(m[10]),&(m[11]),&(m[12]),&(m[13]),&(m[14]),&(m[15]));\
}

/**
 *@ingroup GROUPMatrix4by4
 *@brief Prints matrix elements to the standard output device.
 *
 *Prints matrix elements to the standard output device.
 *
 *@param m  a pointer of type  matrix4by4_t to a 16 element vector.
 *
 *@descript prints the matrix  m as a 4x4 grid of elements.
 */
#define print_matrix4by4(m)\
{\
    printf("[%f, %f, %f, %f]\n[%f, %f, %f, %f]\n[%f, %f, %f, %f]\n[%f, %f, %f, %f]\n",\
            m[0],m[1],m[2],m[3],m[4],m[5],m[6],m[7],m[8],m[9],m[10],m[11],m[12],m[13],m[14],m[15]);\
}

/**
 *@ingroup GROUPMatrix4by4
 *@brief Performs matrix addition, i.e.,  m =  m1 +  m2..
 *
 *Performs matrix addition, i.e.,  m =  m1 +  m2.
 *
 *@param m1 a pointer of type  matrix4by4_t to a 16 element vector.
 *@param m2 a pointer of type  matrix4by4_t to a 16 element vector.
 *@param m  a pointer of type  matrix4by4_t to a 16 element vector.
 */
#define add_matrix4by4(m1,m2,m)\
{\
    m[0]  = m1[0] + m2[0];      m[1]  = m1[1] + m2[1];       m[2]  = m1[2]  + m2[2];    m[3]  = m1[3]  + m2[3];\
    m[4]  = m1[4] + m2[4];      m[5]  = m1[5] + m2[5];       m[6]  = m1[6]  + m2[6];    m[7]  = m1[7]  + m2[7];\
    m[8]  = m1[8] + m2[8];      m[9]  = m1[9] + m2[9];       m[10] = m1[10] + m2[10];   m[11] = m1[11] + m2[11];\
    m[12] = m1[12]+ m2[12];     m[13] = m1[13]+ m2[13];      m[14] = m1[14] + m2[14];   m[15] = m1[15] + m2[15];\
}

/**
 *@ingroup GROUPMatrix4by4
 *@brief Performs matrix subtraction, i.e.,  m =  m1 -  m2..
 *
 *Performs matrix subtraction, i.e.,  m =  m1 -  m2.
 *
 *@param m1 a pointer of type  matrix4by4_t to a 16 element vector.
 *@param m2 a pointer of type  matrix4by4_t to a 16 element vector.
 *@param m  a pointer of type  matrix4by4_t to a 16 element vector.
 */
#define sub_matrix4by4(m1,m2,m)\
{\
    m[0]  = m1[0] - m2[0];      m[1]  = m1[1] - m2[1];       m[2]  = m1[2]  - m2[2];    m[3]  = m1[3]  - m2[3];\
    m[4]  = m1[4] - m2[4];      m[5]  = m1[5] - m2[5];       m[6]  = m1[6]  - m2[6];    m[7]  = m1[7]  - m2[7];\
    m[8]  = m1[8] - m2[8];      m[9]  = m1[9] - m2[9];       m[10] = m1[10] - m2[10];   m[11] = m1[11] - m2[11];\
    m[12] = m1[12]- m2[12];     m[13] = m1[13]- m2[13];      m[14] = m1[14] - m2[14];   m[15] = m1[15] - m2[15];\
}

/**
 *@ingroup GROUPMatrix4by4
 *@brief Multiplies a matrix by a scalar.
 *
 *Multiplies a matrix by a scalar.
 *
 *@param m1 a pointer of type  matrix4by4_t to a 16 element vector.
 *@param d  a scalar value.
 *@param m  a pointer of type  matrix4by4_t to a 16 element vector.
 *
 *@descript multiplies each element of matrix  m by the scalar  d and stores the result in the corresponding element 
 * of matrix  m.
 */
#define multiply_scalar_matrix4by4(m1,d,m)\
{\
    m[0] = m1[0] * (d);      m[1] = m1[1] * (d);       m[2] = m1[2] * (d);      m[3] = m1[3] * (d);\
    m[4] = m1[4] * (d);      m[5] = m1[5] * (d);       m[6] = m1[6] * (d);      m[7] = m1[7] * (d);\
    m[8] = m1[8] * (d);      m[9] = m1[9] * (d);       m[10]= m1[10]* (d);      m[11]= m1[11]* (d);\
    m[12]= m1[12]* (d);      m[13]= m1[13]* (d);       m[14]= m1[14]* (d);      m[15]= m1[15]* (d);\
}
/**
 *@ingroup GROUPMatrix4by4
 *@brief Performs matrix multiplication, i.e.,  m =  m1 *  m2.
 *
 *Performs matrix multiplication, i.e.,  m =  m1 *  m2.
 *
 *@param m1 a pointer of type  matrix4by4_t to a 16 element vector.
 *@param m2 a pointer of type  matrix4by4_t to a 16 element vector.
 *@param m  a pointer of type  matrix4by4_t to a 16 element vector.
 *
 *@warning If  m points to the same matrix as either  m1 or  m2, then the result
 *may be incorrect.
 */
#define multiply_matrix_matrix4by4(m1,m2,m)\
{\
    m[0] = m1[0] * m2[0] + m1[1] * m2[4] + m1[2] * m2[8] + m1[3] * m2[12];\
    m[1] = m1[0] * m2[1] + m1[1] * m2[5] + m1[2] * m2[9] + m1[3] * m2[13];\
    m[2] = m1[0] * m2[2] + m1[1] * m2[6] + m1[2] * m2[10]+ m1[3] * m2[14];\
    m[3] = m1[0] * m2[3] + m1[1] * m2[7] + m1[2] * m2[11]+ m1[3] * m2[15];\
    m[4] = m1[4] * m2[0] + m1[5] * m2[4] + m1[6] * m2[8] + m1[7] * m2[12];\
    m[5] = m1[4] * m2[1] + m1[5] * m2[5] + m1[6] * m2[9] + m1[7] * m2[13];\
    m[6] = m1[4] * m2[2] + m1[5] * m2[6] + m1[6] * m2[10]+ m1[7] * m2[14];\
    m[7] = m1[4] * m2[3] + m1[5] * m2[7] + m1[6] * m2[11]+ m1[7] * m2[15];\
    m[8] = m1[8] * m2[0] + m1[9] * m2[4] + m1[10]* m2[8] + m1[11]* m2[12];\
    m[9] = m1[8] * m2[1] + m1[9] * m2[5] + m1[10]* m2[9] + m1[11]* m2[13];\
    m[10]= m1[8] * m2[2] + m1[9] * m2[6] + m1[10]* m2[10]+ m1[11]* m2[14];\
    m[11]= m1[8] * m2[3] + m1[9] * m2[7] + m1[10]* m2[11]+ m1[11]* m2[15];\
    m[12]= m1[12]* m2[0] + m1[13]* m2[4] + m1[14]* m2[8] + m1[15]* m2[12];\
    m[13]= m1[12]* m2[1] + m1[13]* m2[5] + m1[14]* m2[9] + m1[15]* m2[13];\
    m[14]= m1[12]* m2[2] + m1[13]* m2[6] + m1[14]* m2[10]+ m1[15]* m2[14];\
    m[15]= m1[12]* m2[3] + m1[13]* m2[7] + m1[14]* m2[11]+ m1[15]* m2[15];\
}

/**
 *@ingroup GROUPMatrix4by4
 *@brief Tests for matrix equality.
 *
 *Tests for matrix equality.
 *
 *@param m1 a pointer of type  matrix4by4_t to a 16 element vector.
 *@param m2 a pointer of type  matrix4by4_t to a 16 element vector.
 *@param b  a boolean variable.
 *
 *@descript sets  b to  TRUE iff every element of matrix  m1 is equal to the
 * corresponding element in matrix  m2.
 */
#define equal_matrix4by4(m1,m2,b)\
{\
    b = (m1[0] == m2[0] && m1[1] == m2[1] && m1[2] == m2[2] && m1[3] == m2[3] &&\
         m1[4] == m2[4] && m1[5] == m2[5] && m1[6] == m2[6] && m1[7] == m2[7] &&\
         m1[8] == m2[8] && m1[9] == m2[9] && m1[10]== m2[10]&& m1[11]== m2[11] &&\
         m1[12]== m2[12]&& m1[13]== m2[13]&& m1[14]== m2[14]&& m1[15]== m2[15]);\
}

/**
 *@ingroup GROUPMatrix4by4
 *@brief Copies matrix  m1 into  matrix  m, i.e.,  m = COPY(m1).
 *
 *Copies matrix  m1 into  matrix  m, i.e.,  m = COPY(m1).
 *@param m1 a pointer of type  matrix4by4_t to a 16 element vector.
 *@param m  a pointer of type  matrix4by4_t to a 16 element vector.
 */
#define copy_matrix4by4(m,m1)\
{\
    m[0] = m1[0];      m[1] = m1[1];       m[2] = m1[2];     m[3] = m1[3];\
    m[4] = m1[4];      m[5] = m1[5];       m[6] = m1[6];     m[7] = m1[7];\
    m[8] = m1[8];      m[9] = m1[9];       m[10]= m1[10];    m[11]= m1[11];\
    m[12]= m1[12];     m[13]= m1[13];      m[14]= m1[14];    m[15]= m1[15];\
}
/**
 *@ingroup GROUPMatrix4by4
 *@brief Copies the transpose of matrix  m1 into the matrix  m, i.e.,  m = COPY(TRANSP(m1)).
 *
 *Copies the transpose of matrix  m1 into  matrix m, i.e.,  m = COPY(TRANSP(m1)).
 *
 *@param m1 a pointer of type  matrix4by4_t to a 16 element vector.
 *@param m  a pointer of type  matrix4by4_t to a 16 element vector.
 */
#define copy_transpose_matrix4by4(m,m1)\
{\
    m[0] = m1[0];      m[1] = m1[4];       m[2] = m1[8];      m[3] = m1[12];\
    m[4] = m1[1];      m[5] = m1[5];       m[6] = m1[9];      m[7] = m1[13];\
    m[8] = m1[2];      m[9] = m1[6];       m[10]= m1[10];     m[11]= m1[14];\
    m[12]= m1[3];      m[13]= m1[7];       m[14]= m1[11];     m[15]= m1[15];\
}

/**
 *@ingroup GROUPMatrix4by4
 *@brief Sets every element of matrix  m to 0.
 *
 *Sets every element of matrix  m to 0.
 *
 *@param m  a pointer of type  matrix4by4_t to a 16 element vector.
 */
#define zero_matrix4by4(m)\
{\
    m[0] = m[1] = m[2] = m[3] = m[4] = m[5] = m[6] = m[7] = m[8] = m[9] = m[10] = m[11] = m[12] = m[13] = m[14] = m[15] = 0;\
}

/**
 *@ingroup GROUPMatrix4by4
 *@brief Initializes the matrix  m to the identity matrix.
 *
 *Initializes the matrix  m to the identity matrix.
 *
 *@param m  a pointer of type  matrix4by4_t to a 16 element vector.
 */
#define identity_matrix4by4(m)\
{\
    m[1] = m[2] = m[3] = m[4] = m[6] = m[7] = m[8] = m[9] = m[11] = m[12] = m[13] = m[14] = 0;\
    m[0] = m[5] = m[10] = m[15] = 1;\
}

/**
 *@ingroup GROUPMatrix4by4
 *@brief Sets the matrix  m to the transpose of itself, i.e., m = TRANSP(m).
 *
 *Sets the matrix  m to the transpose of itself.
 *
 *@param m  a pointer of type  matrix4by4_t to a 16 element vector.
 */
#define transpose_matrix4by4(m)\
{\
    double tempM4000;\
    tempM4000 = m[4];  m[4] = m[1];  m[1] = tempM4000;\
    tempM4000 = m[8];  m[8] = m[2];  m[2] = tempM4000;\
    tempM4000 = m[9];  m[9] = m[6];  m[6] = tempM4000;\
    tempM4000 = m[12]; m[12]= m[3];  m[3] = tempM4000;\
    tempM4000 = m[13]; m[13]= m[7];  m[7] = tempM4000;\
    tempM4000 = m[14]; m[15]= m[11]; m[11]= tempM4000;\
}

/**
 *@ingroup GROUPMatrix4by4
 *@brief Rotational matrix along the x-axis.
 *
 *Rotational matrix along the x-axis.
 *
 *@param m   a pointer of type  matrix4by4_t to a 16 element vector.
 *@param rad a scalar value representing an angle in radians.
 *
 *@descript   the matrix  m represents the rotation by an angle of  rad radians in ccw direction
 *through the origin and  along the unit vector parallel to the x-axis.
 */
#define set_rotx_matrix4by4(m,rad)\
{\
    m[0] = m[15] = 1;\
    m[1] = m[2] = m[4] = m[8] = m[3] = m[7] = m[11] = m[12] = m[13] = m[14] = 0;\
    double crM4000 = cosf((float)rad);\
    double srM4001 = sinf((float)rad);\
    m[5] = crM4000;\
    m[6] = -srM4001;\
    m[9] = srM4001;\
    m[10] = crM4000;\
}

/**
 *@ingroup GROUPMatrix4by4
 *@brief Rotational matrix along the y-axis.
 *
 *Rotational matrix along the y-axis.
 *
 *@param m   a pointer of type  matrix4by4_t to a 16 element vector.
 *@param rad a scalar value representing an angle in radians.
 *
 *@descript   the matrix  m represents the rotation by an angle of   rad radians in ccw direction
 *through the origin and  along the unit vector parallel to the y-axix.
 */
#define set_roty_matrix4by4(m,rad)\
{\
    m[5] = m[15] = 1;\
    m[1] = m[4] = m[6] = m[9] = m[3] = m[7] = m[11] = m[12] = m[13] = m[14] = 0;\
    double crM4000 = cosf((float)rad);\
    double srM4001 = sinf((float)rad);\
    m[0] = crM4000;\
    m[2] = srM4001;\
    m[8] = -srM4001;\
    m[10] = crM4000;\
}

/**
 *@ingroup GROUPMatrix4by4
 *@brief Rotational matrix along the z-axis.
 *
 *Rotational matrix along the z-axis.
 *
 *@param m   a pointer of type  matrix4by4_t to a 16 element vector.
 *@param rad a scalar value representing an angle in radians.
 *
 *@descript   the matrix  m represents the rotation by an angle of   rad radians in ccw direction
 * through the origin and along the unit vector parallel to the z-axis.
 */
#define set_rotz_matrix4by4(m,rad)\
{\
    m[10] = m[15] = 1;\
    m[2] = m[6] = m[8] = m[9] = m[3] = m[7] = m[11] = m[12] = m[13] = m[14] = 0;\
    double crM4000 = cosf((float)rad);\
    double srM4001 = sinf((float)rad);\
    m[0] = crM4000;\
    m[4] = srM4001;\
    m[1] = -srM4001;\
    m[5] = crM4000;\
}

/**
 *@ingroup GROUPMatrix4by4
 *@brief Rotational matrix along an arbitrary unit axis.
 *
 *Rotational matrix along an arbitrary unit axis.
 *
 *@param m   a pointer of type  matrix4by4_t to a 16 element vector.
 *@param ax  a 3-dimensional unit vector.
 *@param rad a scalar value representing an angle in radians.
 *
 *@descript   the matrix  m represents the rotation by an angle of   rad radians in ccw direction
 * through the origin and along the unit vector  ax.
 */
#define set_rotation_matrix4by4(m,ax,rad)\
{\
    double cM4000 = cosf((float)rad);\
    double sM4001 = sinf((float)rad);\
    double tM4002 = 1.0f - cM4000;\
    m[0] = tM4002*ax[0]*ax[0]+cM4000;       m[1] = tM4002*ax[1]*ax[0]-sM4001*ax[2]; m[2] = tM4002*ax[2]*ax[0]+sM4001*ax[1];\
    m[4] = tM4002*ax[0]*ax[1]+sM4001*ax[2]; m[5] = tM4002*ax[1]*ax[1]+cM4000; 	  m[6] = tM4002*ax[2]*ax[1]-sM4001*ax[0];\
    m[8] = tM4002*ax[0]*ax[2]-sM4001*ax[1]; m[9] = tM4002*ax[1]*ax[2]+sM4001*ax[0]; m[10] = tM4002*ax[2]*ax[2]+cM4000;\
    m[3] = m[7] = m[11] = m[12] = m[13] = m[14] = 0;\
    m[15] = 1;\
}

/**
 *@ingroup GROUPMatrix4by4
 *@brief Translational matrix.
 *
 *Translational matrix.
 *
 *@param m   a pointer of type  matrix4by4_t to a 16 element vector.
 *@param v   a 3-dimensional vector.
 *
 *@descript   the matrix  m represents the translation by the vector  v.
 */
#define set_translation_matrix4by4(m,v)\
{\
    m[0] = m[5] = m[10] = m[15] = 1;\
    m[1] = m[2] = m[4] = m[6] = m[8] = m[9] = m[12] = m[13] = m[14] = 0;\
    m[3] = v[0];\
    m[7] = v[1];\
    m[11] = v[2];\
}

/**
 *@ingroup GROUPMatrix4by4
 *@brief Rotation followed by translation.
 *
 *Rotation followed by translation.
 *
 *@param m   a pointer of type  matrix4by4_t to a 16 element vector.
 *@param ax  a 3-dimensional unit vector.
 *@param rad a scalar value representing an angle in radians.
 *@param v   a 3-dimensional vector.
 *
 *@descript    the matrix  m represents the rotation by an angle of   rad radians in ccw direction
 * through the origin and along the unit vector  ax followed by a translation by the vector  v.
 */
#define set_rotation_translation_matrix4by4(m,ax,rad,v)\
{\
    double cM4000 = cosf((float)rad);\
    double sM4001 = sinf((float)rad);\
    double tM4002 = 1.0f - cM4000;\
    m[0] = tM4002*ax[0]*ax[0]+cM4000;       m[1] = tM4002*ax[1]*ax[0]-sM4001*ax[2]; m[2] = tM4002*ax[2]*ax[0]+sM4001*ax[1];\
    m[4] = tM4002*ax[0]*ax[1]+sM4001*ax[2]; m[5] = tM4002*ax[1]*ax[1]+cM4000; 	  m[6] = tM4002*ax[2]*ax[1]-sM4001*ax[0];\
    m[8] = tM4002*ax[0]*ax[2]-sM4001*ax[1]; m[9] = tM4002*ax[1]*ax[2]+sM4001*ax[0]; m[10] = tM4002*ax[2]*ax[2]+cM4000;\
    m[12] = m[13] = m[14] = 0;\
    m[15] = 1;\
    m[3] = v[0];\
    m[7] = v[1];\
    m[11] = v[2];\
}


/**
 *@ingroup GROUPMatrix4by4
 *@brief Translation followed by rotation.
 *
 *Translation followed by rotation.
 *
 *@param m   a pointer of type  matrix4by4_t to a 16 element vector.
 *@param v   a 3-dimensional vector.
 *@param ax  a 3-dimensional unit vector.
 *@param rad a scalar value representing an angle in radians.
 *
 *@descript    the matrix  m represents the translation by the vector  v followed by the
 * rotation by an angle of   rad radians in ccw direction
 * through the origin and along the unit vector  ax.
 */
#define set_translation_rotation_matrix4by4(m, v, ax,rad)\
{\
    double cM4000 = cosf((float)rad);\
    double sM4001 = sinf((float)rad);\
    double tM4002 = 1.0f - cM4000;\
    m[0] = tM4002*ax[0]*ax[0]+cM4000;       m[1] = tM4002*ax[1]*ax[0]-sM4001*ax[2]; m[2] = tM4002*ax[2]*ax[0]+sM4001*ax[1];\
    m[4] = tM4002*ax[0]*ax[1]+sM4001*ax[2]; m[5] = tM4002*ax[1]*ax[1]+cM4000; 	  m[6] = tM4002*ax[2]*ax[1]-sM4001*ax[0];\
    m[8] = tM4002*ax[0]*ax[2]-sM4001*ax[1]; m[9] = tM4002*ax[1]*ax[2]+sM4001*ax[0]; m[10] = tM4002*ax[2]*ax[2]+cM4000;\
    m[12] = m[13] = m[14] = 0;\
    m[3] = m[0]*v[0] + m[1]*v[1] + m[2]*v[2];\
    m[7] = m[4]*v[0] + m[5]*v[1] + m[6]*v[2];\
    m[11] = m[8]*v[0] + m[9]*v[1] + m[10]*v[2];\
    m[15] = 1;\
}
/**
 *@ingroup GROUPMatrix4by4
 *@brief Scaling matrix.
 *
 *Scaling matrix.
 *
 *@param m   a pointer of type  matrix4by4_t to a 16 element vector.
 *@param sx  a scalar value representing scaling in x-direction.
 *@param sy  a scalar value representing scaling in y-direction.
 *@param sz  a scalar value representing scaling in z-direction.
 *
 *@descript   the matrix  m represents scaling through the origin by  sx in the x-direction,
 *  sy in the y-direction, and   sz in the z-direction. 
 */
#define set_scale_matrix4by4(m,sx,sy,sz)\
{\
    m[1] = m[2] = m[4] = m[6] = m[8] = m[9] = m[3] = m[7] = m[11] = m[12] = m[13] = m[14] = 0;\
    m[0] = sx;\
    m[5] = sy;\
    m[10] = sz;\
    m[15] = 1;\
}

/**
 *@ingroup GROUPMatrix4by4
 *@brief Converts a 3x3 matrix to a 4x4 matrix that represents the same transformation.
 *
 *Converts a 3x3 matrix to a 4x4 matrix that represents the same transformation.
 *
 *@param m   a pointer of type  matrix4by4_t to a 16 element vector.
 *@param m1  a pointer of type  matrix3by3_t to a  9 element vector.
 */
#define from_3by3_matrix4by4(m,m1)\
{\
 m[0] = m1[0];  m[1] = m1[1]; m[2] = m1[2];\
 m[4] = m1[3];  m[5] = m1[4]; m[6] = m1[5];\
 m[8] = m1[6];  m[9] = m1[7]; m[10]= m1[8];\
 m[3] = m[7] = m[11] = m[12] = m[13] = m[14] = 0;\
 m[15]= 1;\
}

#define cofactor3(a0,a1,a2,a3,a4,a5,a6,a7,a8)\
(\
  (a0)*((a4)*(a8)-(a5)*(a7)) - (a3)*((a1)*(a8)-(a2)*(a7)) + (a6)*((a1)*(a5) - (a2)*(a4))\
)

#define cofactor00(m) cofactor3(m[5],m[6],m[7],m[9],m[10],m[11],m[13],m[14],m[15])
#define cofactor01(m) cofactor3(m[4],m[6],m[7],m[8],m[10],m[11],m[12],m[14],m[15])
#define cofactor02(m) cofactor3(m[4],m[5],m[7],m[8],m[9], m[11],m[12],m[13],m[15])
#define cofactor03(m) cofactor3(m[4],m[5],m[6],m[8],m[9], m[10],m[12],m[13],m[14])

#define cofactor10(m) cofactor3(m[1],m[2],m[3],m[9],m[10],m[11],m[13],m[14],m[15])
#define cofactor11(m) cofactor3(m[0],m[2],m[3],m[8],m[10],m[11],m[12],m[14],m[15])
#define cofactor12(m) cofactor3(m[0],m[1],m[3],m[8],m[9], m[11],m[12],m[13],m[15])
#define cofactor13(m) cofactor3(m[0],m[1],m[2],m[8],m[9], m[10],m[12],m[13],m[14])

#define cofactor20(m) cofactor3(m[1],m[2],m[3],m[5],m[6], m[7],m[13],m[14],m[15])
#define cofactor21(m) cofactor3(m[0],m[2],m[3],m[4],m[6], m[7],m[12],m[14],m[15])
#define cofactor22(m) cofactor3(m[0],m[1],m[3],m[4],m[5], m[7],m[12],m[13],m[15])
#define cofactor23(m) cofactor3(m[0],m[1],m[2],m[4],m[5], m[6],m[12],m[13],m[14])

#define cofactor30(m) cofactor3(m[1],m[2],m[3],m[5],m[6], m[7],m[9],m[10],m[11])
#define cofactor31(m) cofactor3(m[0],m[2],m[3],m[4],m[6], m[7],m[8],m[10],m[11])
#define cofactor32(m) cofactor3(m[0],m[1],m[3],m[4],m[5], m[7],m[8],m[9], m[11])
#define cofactor33(m) cofactor3(m[0],m[1],m[2],m[4],m[5], m[6],m[8],m[9], m[10])

/**
 *@ingroup GROUPMatrix4by4
 *@brief Calculates the determinant.
 *
 *Calculates the determinant.
 *
 *@param m   a pointer of type  matrix4by4_t to a 16 element vector.
 *@param det an out variable of type double.
 *
 *@return   the determinant of the matrix  m.
 */
#define calc_determinant_matrix4by4(m,det)\
{\
    det = m[0]*cofactor00(m) - m[4]*cofactor10(m) + m[8]*cofactor20(m) - m[12]*cofactor30(m);\
}

/**
 *@ingroup GROUPMatrix4by4
 *@brief Computes the inverse matrix, i.e.,  m = INVERSE(m1).
 *
 *Computes the inverse matrix, i.e.,  m = INVERSE(m1).
 *
 *@param m   a pointer of type  matrix4by4_t to a 16 element vector.
 *@param m1  a pointer of type  matrix4by4_t to a 16 element vector.
 *
 *@descript  the (i,j)-th entry of the inverse of  m1 is equal to ADJ(m1, i, j)/DET(m1).
 *
 *@warning If  m points to the same matrix as m1, then the result may be incorrect.
 */
#define invert_square_matrix4by4(m,m1)\
{\
    double detM4000;\
    calc_determinant_matrix4by4(m1,detM4000);\
    if(detM4000 == 0)\
     printf("4by4 matrix is singular\n");\
    else\
    {\
     m[0] = (+(cofactor00(m1)))/detM4000;  m[4] = (-(cofactor01(m1)))/detM4000;\
     m[1] = (-(cofactor10(m1)))/detM4000;  m[5] = (+(cofactor11(m1)))/detM4000;\
     m[2] = (+(cofactor20(m1)))/detM4000;  m[6] = (-(cofactor21(m1)))/detM4000;\
     m[3] = (-(cofactor30(m1)))/detM4000;  m[7] = (+(cofactor31(m1)))/detM4000;\
     m[8] = (+(cofactor02(m1)))/detM4000;  m[12]= (-(cofactor03(m1)))/detM4000;\
     m[9] = (-(cofactor12(m1)))/detM4000;  m[13]= (+(cofactor13(m1)))/detM4000;\
     m[10]= (+(cofactor22(m1)))/detM4000;  m[14]= (-(cofactor23(m1)))/detM4000;\
     m[11]= (-(cofactor32(m1)))/detM4000;  m[15]= (+(cofactor33(m1)))/detM4000;\
      printf("[%f, %f, %f, %f]\n[%f, %f, %f, %f]\n[%f, %f, %f, %f]\n[%f, %f, %f, %f]\n",\
            cofactor00(m1),cofactor01(m1),cofactor02(m1), cofactor03(m1),\
            cofactor10(m1),cofactor11(m1),cofactor12(m1), cofactor13(m1),\
            cofactor20(m1),cofactor21(m1),cofactor22(m1), cofactor23(m1),\
            cofactor30(m1),cofactor31(m1),cofactor32(m1), cofactor33(m1));\
   }\
}

/**
 *@ingroup GROUPMatrix4by4
 *@brief Transform a 3d vector by a 4by4 matrix.
 *
 *Transform a 3d vector by a 4by4 matrix.
 *
 *@param v1  a 3d vector 
 *@param m   a pointer of type  matrix4by4_t to a 16 element vector.
 *@param v   the resulting 3d vector
 *
 */
#define transform_vector3d_matrix4by4(v1,m,v)\
{\
    v[0] = v1[0] * m[0]  + v1[1] * m[1] + v1[2] * m[2];\
    v[1] = v1[0] * m[4]  + v1[1] * m[5] + v1[2] * m[6];\
    v[2] = v1[0] * m[8]  + v1[1] * m[9] + v1[2] * m[10];\
}

/**
 *@ingroup GROUPMatrix4by4
 *@brief Transform a 3d vector by a 4by4 matrix.
 *
 *Transform a 3d vector by a 4by4 matrix.
 *
 *@param v1  a 3d vector 
 *@param m   a pointer of type  matrix4by4_t to a 16 element vector.
 *@param v   the resulting 3d vector
 *
 */
#define transform_point3d_matrix4by4(v1,m,v)\
{\
    v[0] = v1[0] * m[0]  + v1[1] * m[1] + v1[2] * m[2]  + m[3];\
    v[1] = v1[0] * m[4]  + v1[1] * m[5] + v1[2] * m[6]  + m[7];\
    v[2] = v1[0] * m[8]  + v1[1] * m[9] + v1[2] * m[10] + m[11];\
}


//END_C_DECL

#endif

