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


#ifndef ___MATRIX3BY3_H__ABCDEEDCBA_
#define ___MATRIX3BY3_H__ABCDEEDCBA_


#include <stdio.h>
#include <stdlib.h>
#include <math.h>

//BEGIN_C_DECL

/** 
 *@defgroup GROUPMatrix3by3 Fast 3x3 matrix operations.
 */

/**
 * @ingroup GROUPMatrix3by3
 * Defining 3x3 matrices as pointers to  double.
 */
typedef double * matrix3by3_t;

/**
 *@ingroup GROUPMatrix3by3
 *@brief Access matrix element, i.e., m[r][c].
 *
 *Access matrix element. i.e.,   m[r][c] .
 *
 *@param m a pointer of type  matrix3by3_t to a 9 element vector.
 *@param r an integer in the range 0...3 representing row index.
 *@param c an integer in the range 0...3 representing column index.
 *
 *@returns the element in row  r and column  c of matrix  m.
 */

#define get_elem_matrix3by3(m, r, c)\
(m[(r)*3 + (c)])

/**
 *@ingroup GROUPMatrix3by3
 *@brief Set matrix element, i.e., m[r][c] = v.
 *
 *Set matrix element, i.e.,  m[r][c] = v .
 *
 *@param m  a pointer of type  matrix3by3_t to a 9 element vector.
 *@param r an integer in the range 0...3 representing row index.
 *@param c an integer in the range 0...3 representing column index.
 *@param v a double.
 * 
 *@descript sets the value of the element in row  r and column  c of matrix  m  to  v.
 */
#define set_elem_matrix3by3(m, r, c, v)\
{\
    m[(r)*3 + (c)] = v;\
}


/**
 *@ingroup GROUPMatrix3by3
 *@brief Allocate memory.
 *
 *Allocate memory.
 *@param m a pointer of type  matrix3by3_t to which no memory has been allocated.
 *@param t element type, i.e.,  double,  float,  int, etc.
 *
 *@descript allocates to  m  a contigous block of 9 elements of type  t.
 */
#define alloc_matrix3by3(m,t)\
{\
    m = (t*)malloc(9*sizeof(t));\
}

/**
 *@ingroup GROUPMatrix3by3
 *@brief Free memory.
 *
 *Free memory.
 *
 *@param m  a pointer of type  matrix3by3_t to a 9 element vector.
 *
 *@descript frees the memory allocated to  m.
 */
#define free_matrix3by3(m)\
{\
    if(m) {free(m); m = NULL;}\
}

/**
 *@ingroup GROUPMatrix3by3
 *@brief Reads matrix elements from a file stream.
 *
 *Reads matrix elements from a file stream.
 *@param m  a pointer of type  matrix3by3_t to a 9 element vector.
 *@param in a pointer to a file.
 *
 *@descript reads the 9 elements of matrix  m from the file to which  in points to.
 */
#define read_matrix3by3(m,input)\
{\
    fscanf( input, "%lf %lf %lf %lf %lf %lf %lf %lf %lf",\
    &(m[0]),&(m[1]),&(m[2]),&(m[3]),&(m[4]),&(m[5]),&(m[6]),&(m[7]),&(m[8]));\
}

/**
 *@ingroup GROUPMatrix3by3
 *@brief Prints matrix elements to the standard output device.
 *
 *Prints matrix elements to the standard output device.
 *
 *@param m  a pointer of type  matrix3by3_t to a 9 element vector.
 *
 *@descript prints the matrix  m as a 3x3 grid of elements.
 */
#define print_matrix3by3(m)\
{\
    printf("[%f, %f, %f]\n[%f, %f, %f]\n[%f, %f, %f]\n",\
            m[0],m[1],m[2],m[3],m[4],m[5],m[6],m[7],m[8]);\
}

/**
 *@ingroup GROUPMatrix3by3
 *@brief Performs matrix addition, i.e.,  m =  m1 +  m2..
 *
 *Performs matrix addition, i.e.,  m =  m1 +  m2.
 *
 *@param m1 a pointer of type  matrix3by3_t to a 9 element vector.
 *@param m2 a pointer of type  matrix3by3_t to a 9 element vector.
 *@param m  a pointer of type  matrix3by3_t to a 9 element vector.
 */
#define add_matrix3by3(m1,m2,m)\
{\
    m[0]  = m1[0] + m2[0];      m[1]  = m1[1] + m2[1];       m[2] = m1[2] + m2[2];\
    m[3]  = m1[3] + m2[3];      m[4]  = m1[4] + m2[4];       m[5] = m1[5] + m2[5];\
    m[6]  = m1[6] + m2[6];      m[7]  = m1[7] + m2[7];       m[8] = m1[8] + m2[8];\
}


/**
 *@ingroup GROUPMatrix3by3
 *@brief Performs matrix subtraction, i.e.,  m =  m1 -  m2..
 *
 *Performs matrix subtraction, i.e.,  m =  m1 -  m2.
 *
 *@param m1 a pointer of type  matrix3by3_t to a 9 element vector.
 *@param m2 a pointer of type  matrix3by3_t to a 9 element vector.
 *@param m  a pointer of type  matrix3by3_t to a 9 element vector.
 */
#define sub_matrix3by3(m1,m2,m)\
{\
    m[0]  = m1[0] - m2[0];      m[1]  = m1[1] - m2[1];       m[2] = m1[2] - m2[2];\
    m[3]  = m1[3] - m2[3];      m[4]  = m1[4] - m2[4];       m[5] = m1[5] - m2[5];\
    m[6]  = m1[6] - m2[6];      m[7]  = m1[7] - m2[7];       m[8] = m1[8] - m2[8];\
}

/**
 *@ingroup GROUPMatrix3by3
 *@brief Multiplies a matrix by a scalar.
 *
 *Multiplies a matrix by a scalar.
 *
 *@param m1 a pointer of type  matrix3by3_t to a 9 element vector.
 *@param d  a scalar value.
 *@param m  a pointer of type  matrix3by3_t to a 9 element vector.
 */
#define multiply_scalar_matrix3by3(m1,d,m)\
{\
    m[0]  = m1[0] * (d);      m[1]  = m1[1] * (d);       m[2] = m1[2] * (d);\
    m[3]  = m1[3] * (d);      m[4]  = m1[4] * (d);       m[5] = m1[5] * (d);\
    m[6]  = m1[6] * (d);      m[7]  = m1[7] * (d);       m[8] = m1[8] * (d);\
}

/**
 *@ingroup GROUPMatrix3by3
 *@brief Performs matrix multiplication, i.e.,  m =  m1 *  m2.
 *
 *Performs matrix multiplication, i.e.,  m =  m1 *  m2.
 *
 *@param m1 a pointer of type  matrix3by3_t to a 9 element vector.
 *@param m2 a pointer of type  matrix3by3_t to a 9 element vector.
 *@param m  a pointer of type  matrix3by3_t to a 9 element vector.
 *
 *@warning If  m points to the same matrix as either  m1 or  m2, then the result
 *may be incorrect.
 */
#define multiply_matrix_matrix3by3(m1,m2,m)\
{\
    m[0] = m1[0] * m2[0] + m1[1] * m2[3] + m1[2] * m2[6];\
    m[1] = m1[0] * m2[1] + m1[1] * m2[4] + m1[2] * m2[7];\
    m[2] = m1[0] * m2[2] + m1[1] * m2[5] + m1[2] * m2[8];\
    m[3] = m1[3] * m2[0] + m1[4] * m2[3] + m1[5] * m2[6];\
    m[4] = m1[3] * m2[1] + m1[4] * m2[4] + m1[5] * m2[7];\
    m[5] = m1[3] * m2[2] + m1[4] * m2[5] + m1[5] * m2[8];\
    m[6] = m1[6] * m2[0] + m1[7] * m2[3] + m1[8] * m2[6];\
    m[7] = m1[6] * m2[1] + m1[7] * m2[4] + m1[8] * m2[7];\
    m[8] = m1[6] * m2[2] + m1[7] * m2[5] + m1[8] * m2[8];\
}

/**
 *@ingroup GROUPMatrix3by3
 *@brief Tests for matrix equality.
 *
 *Tests for matrix equality.
 *
 *@param m1 a pointer of type  matrix3by3_t to a 9 element vector.
 *@param m2 a pointer of type  matrix3by3_t to a 9 element vector.
 *@param b  a boolean variable.
 *
 *@descript sets  b to  TRUE iff every element of matrix  m1 is equal to the
 * corresponding element in matrix  m2.
 */
#define equal_matrix3by3(m1,m2,b)\
{\
    b = (m1[0] == m2[0] && m1[1] == m2[1] && m1[2] == m2[2] &&\
         m1[3] == m2[3] && m1[4] == m2[4] && m1[5] == m2[5] &&\
         m1[6] == m2[6] && m1[7] == m2[7] && m1[8] == m2[8] );\
}

/**
 *@ingroup GROUPMatrix3by3
 *@brief Copies matrix  m1 into  matrix  m, i.e.,  m = COPY(m1).
 *
 *Copies matrix  m1 into  matrix  m, i.e.,  m = COPY(m1).
 *
 *@param m1 a pointer of type  matrix3by3_t to a 9 element vector.
 *@param m  a pointer of type  matrix3by3_t to a 9 element vector.
 */
#define copy_matrix3by3(m,m1)\
{\
    m[0] = m1[0];      m[1] = m1[1];       m[2] = m1[2];\
    m[3] = m1[3];      m[4] = m1[4];       m[5] = m1[5];\
    m[6] = m1[6];      m[7] = m1[7];       m[8] = m1[8];\
}
/**
 *@ingroup GROUPMatrix3by3
 *@brief Copies the transpose of matrix  m1 into the matrix  m, i.e.,  m = COPY(TRANSP(m1)).
 *
 *Copies the transpose of matrix  m1 into  matrix m, i.e.,  m = COPY(TRANSP(m1)).
 *
 *@param m1 a pointer of type  matrix3by3_t to a 9 element vector.
 *@param m  a pointer of type  matrix3by3_t to a 9 element vector.
 */
#define copy_transpose_matrix3by3(m,m1)\
{\
    m[0] = m1[0];      m[1] = m1[3];       m[2] = m1[6];\
    m[3] = m1[1];      m[4] = m1[4];       m[5] = m1[7];\
    m[6] = m1[2];      m[7] = m1[5];       m[8] = m1[8];\
}

/**
 *@ingroup GROUPMatrix3by3
 *@brief Sets every element of matrix  m to 0.
 *
 *Sets every element of matrix  m to 0.
 *
 *@param m  a pointer of type  matrix3by3_t to a 9 element vector.
 */
#define zero_matrix3by3(m)\
{\
    m[0] = m[1] = m[2] = m[3] = m[4] = m[5] = m[6] = m[7] = m[8] = 0;\
}

/**
 *@ingroup GROUPMatrix3by3
 *@brief Initializes the matrix  m to the identity matrix.
 *
 *Initializes the matrix  m to the identity matrix.
 *
 *@param m  a pointer of type  matrix3by3_t to a 9 element vector.
 */
#define identity_matrix3by3(m)\
{\
    m[1] = m[2] = m[3] = m[5] = m[6] = m[7] = 0;\
    m[0] = m[4] = m[8] = 1;\
}
/**
 *@ingroup GROUPMatrix3by3
 *@brief Sets the matrix  m to the transpose of itself, i.e., m = TRANSP(m).
 *
 *Sets the matrix  m to the transpose of itself.
 *
 *@param m  a pointer of type  matrix3by3_t to a 9 element vector.
 */
#define transpose_matrix3by3(m)\
{\
    double tempM3000;\
    tempM3000 = m[3];    m[3] = m[1];    m[1] = tempM3000;\
    tempM3000 = m[6];    m[6] = m[2];    m[2] = tempM3000;\
    tempM3000 = m[7];    m[7] = m[5];    m[5] = tempM3000;\
}

/**
 *@ingroup GROUPMatrix3by3
 *@brief Rotational matrix along the x-axis.
 *
 *Rotational matrix along the x-axis.
 *
 *@param m   a pointer of type  matrix3by3_t to a 9 element vector.
 *@param rad a scalar value representing an angle in radians.
 *
 *@descript   the matrix  m represents the rotation by an angle of  rad radians in ccw direction
 *through the origin and  along the unit vector parallel to the x-axis.
 */
#define set_rotx_matrix3by3(m,rad)\
{\
    m[0] = 1;\
    m[1] = m[2] = m[3] = m[6] = 0;\
    double crM3000 = cosf((float)rad);\
    double srM3001 = sinf((float)rad);\
    m[4] = crM3000;\
    m[5] = -srM3001;\
    m[7] = srM3001;\
    m[8] = crM3000;\
}

/**
 *@ingroup GROUPMatrix3by3
 *@brief Rotational matrix along the y-axis.
 *
 *Rotational matrix along the y-axis.
 *
 *@param m   a pointer of type  matrix3by3_t to a 9 element vector.
 *@param rad a scalar value representing an angle in radians.
 *
 *@descript   the matrix  m represents the rotation by an angle of   rad radians in ccw direction
 *through the origin and  along the unit vector parallel to the y-axix.
 */
#define set_roty_matrix3by3(m,rad)\
{\
    m[4] = 1;\
    m[1] = m[3] = m[5] = m[7] = 0;\
    double crM3000 = cosf((float)rad);\
    double srM3001 = sinf((float)rad);\
    m[0] = crM3000;\
    m[2] = srM3001;\
    m[6] = -srM3001;\
    m[8] = crM3000;\
}

/**
 *@ingroup GROUPMatrix3by3
 *@brief Rotational matrix along the z-axis.
 *
 *Rotational matrix along the z-axis.
 *
 *@param m   a pointer of type  matrix3by3_t to a 9 element vector.
 *@param rad a scalar value representing an angle in radians.
 *
 *@descript   the matrix  m represents the rotation by an angle of   rad radians in ccw direction
 * through the origin and along the unit vector parallel to the z-axis.
 */
#define set_rotz_matrix3by3(m,rad)\
{\
    m[8] = 1;\
    m[2] = m[5] = m[6] = m[7] = 0;\
    double crM3000 = cosf((float)rad);\
    double srM3001 = sinf((float)rad);\
    m[0] = crM3000;\
    m[3] = srM3001;\
    m[1] = -srM3001;\
    m[4] = crM3000;\
}

/**
 *@ingroup GROUPMatrix3by3
 *@brief Rotational matrix along an arbitrary  unit axis.
 *
 *Rotational matrix along an arbitrary  unit axis.
 *
 *@param m   a pointer of type  matrix3by3_t to a 9 element vector.
 *@param ax  a 3-dimensional unit vector.
 *@param rad a scalar value representing an angle in radians.
 *
 *@descript   the matrix  m represents the rotation by an angle of   rad radians in ccw direction
 * through the origin and along the unit vector  ax.
 */
#define set_rotation_matrix3by3(m,ax,rad)\
{\
    double cM3000 = cosf((float)rad);\
    double sM3001 = sinf((float)rad);\
    double tM3002 = 1.0f - cM3000;\
    m[0] = tM3002*ax[0]*ax[0]+cM3000;       m[1] = tM3002*ax[1]*ax[0]-sM3001*ax[2]; m[2] = tM3002*ax[2]*ax[0]+sM3001*ax[1];\
    m[3] = tM3002*ax[0]*ax[1]+sM3001*ax[2]; m[4] = tM3002*ax[1]*ax[1]+cM3000;       m[5] = tM3002*ax[2]*ax[1]-sM3001*ax[0];\
    m[6] = tM3002*ax[0]*ax[2]-sM3001*ax[1]; m[7] = tM3002*ax[1]*ax[2]+sM3001*ax[0]; m[8] = tM3002*ax[2]*ax[2]+cM3000;\
}

/**
 *@ingroup GROUPMatrix3by3
 *@brief Scaling matrix.
 *
 *Scaling matrix.
 *
 *@param m   a pointer of type  matrix3by3_t to a 9 element vector.
 *@param sx  a scalar value representing scaling in x-direction.
 *@param sy  a scalar value representing scaling in y-direction.
 *@param sz  a scalar value representing scaling in z-direction.
 *
 *@descript   the matrix  m represents scaling through the origin by  sx in the x-direction,
 *  sy in the y-direction, and   sz in the z-direction. 
 */
#define set_scale_matrix3by3(m,sx,sy,sz)\
{\
    m[1] = m[2] = m[3] = m[5] = m[6] = m[7] = 0;\
    m[0] = sx;\
    m[4] = sy;\
    m[8] = sz;\
}

/**
 *@ingroup GROUPMatrix3by3
 *@brief Calculates the determinant.
 *
 *Calculates the determinant.
 *
 *@param m   a pointer of type  matrix3by3_t to a 9 element vector.
 *@param det an out variable of type double.
 *
 *@return   the determinant of the matrix  m.
 */
#define calc_determinant_matrix3by3(m,det)\
{\
    det = m[0]*(m[4]*m[8] - m[7]*m[5]) - m[1]*(m[3]*m[8] - m[6]*m[5]) +  m[2]*(m[3]*m[7] - m[6]*m[4]);\
}

/**
 *@ingroup GROUPMatrix3by3
 *@brief Computes the inverse matrix, i.e.,  m = INVERSE(m1).
 *
 *Computes the inverse matrix, i.e.,  m = INVERSE(m1).
 *
 *@param m   a pointer of type  matrix3by3_t to a 9 element vector.
 *@param m1  a pointer of type  matrix3by3_t to a 9 element vector.
 *
 *@descript  the (i,j)-th entry of the inverse of  m1 is equal to ADJ(m1, i, j)/DET(m1).
 *
 *@warning If  m points to the same matrix as m1, then the result may be incorrect.
 */
#define invert_square_matrix3by3(m,m1)\
{\
    double detM3000;\
    calc_determinant_matrix3by3(m1,detM3000);\
    if( detM3000 != 0 )\
    {\
	m[0] =  (m1[4]*m1[8] - m1[5]*m1[7]) / detM3000;\
	m[1] = -(m1[1]*m1[8] - m1[2]*m1[7]) / detM3000;\
	m[2] =  (m1[1]*m1[5] - m1[4]*m1[2]) / detM3000;\
	m[3] = -(m1[3]*m1[8] - m1[5]*m1[6]) / detM3000;\
	m[4] =  (m1[0]*m1[8] - m1[2]*m1[6]) / detM3000;\
	m[5] = -(m1[0]*m1[5] - m1[3]*m1[2]) / detM3000;\
	m[6] =  (m1[3]*m1[7] - m1[4]*m1[6]) / detM3000;\
	m[7] = -(m1[0]*m1[7] - m1[1]*m1[6]) / detM3000;\
	m[8] =  (m1[0]*m1[4] - m1[1]*m1[3]) / detM3000;\
    }\
    else\
	printf("DET = 0!!!! I cannot invert this matrix\n");\
}

//END_C_DECL

#endif
