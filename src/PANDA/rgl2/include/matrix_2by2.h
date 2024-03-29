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


#ifndef ___MATRIX2BY2_H__ABCDEEDCBA_
#define ___MATRIX2BY2_H__ABCDEEDCBA_

#include <stdio.h>
#include <stdlib.h>
#include <math.h>

//BEGIN_C_DECL

/** 
 *@defgroup GROUPMatrix2by2 Fast 2x2 matrix operations.
 */

/**
 * @ingroup GROUPMatrix2by2
 * Defining 2x2 matrices as pointers to  double.
 */
typedef double * matrix2by2_t;

/**
 *@ingroup GROUPMatrix2by2
 *@brief Access matrix element, i.e., m[r][c].
 *
 *Access matrix element. i.e.,   m[r][c] .
 *
 *@param m a pointer of type  matrix2by2_t to a 4 element vector.
 *@param r an integer in the range 0...3 representing row index.
 *@param c an integer in the range 0...3 representing column index.
 *
 *@returns the element in row  r and column  c of matrix  m.
 */

#define get_elem_matrix2by2(m, r, c)\
(m[(r)*2 + (c)])

/**
 *@ingroup GROUPMatrix2by2
 *@brief Set matrix element, i.e., m[r][c] = v.
 *
 *Set matrix element, i.e.,  m[r][c] = v .
 *
 *@param m  a pointer of type  matrix2by2_t to a 4 element vector.
 *@param r an integer in the range 0...1 representing row index.
 *@param c an integer in the range 0...1 representing column index.
 *@param v a double.
 * 
 *@descript sets the value of the element in row  r and column  c of matrix  m  to  v.
 */
#define set_elem_matrix2by2(m, r, c, v)\
{\
    m[(r)*2 + (c)] = v;\
}


/**
 *@ingroup GROUPMatrix2by2
 *@brief Allocate memory.
 *
 *Allocate memory.
 *@param m a pointer of type  matrix2by2_t to which no memory has been allocated.
 *@param t element type, i.e.,  double,  float,  int, etc.
 *
 *@descript allocates to  m  a contigous block of 4 elements of type  t.
 */
#define alloc_matrix2by2(m,t)\
{\
    m = (t*)malloc(4*sizeof(t));\
}

/**
 *@ingroup GROUPMatrix2by2
 *@brief Free memory.
 *
 *Free memory.
 *
 *@param m  a pointer of type  matrix2by2_t to a 4 element vector.
 *
 *@descript frees the memory allocated to  m.
 */
#define free_matrix2by2(m)\
{\
    if(m) {free(m); m = NULL;}\
}

/**
 *@ingroup GROUPMatrix2by2
 *@brief Reads matrix elements from a file stream.
 *
 *Reads matrix elements from a file stream.
 *@param m  a pointer of type  matrix2by2_t to a 4 element vector.
 *@param in a pointer to a file.
 *
 *@descript reads the 4 elements of matrix  m from the file to which  in points to.
 */
#define read_matrix2by2(m,input)\
{\
    fscanf( input, "%lf %lf %lf %lf",&(m[0]),&(m[1]),&(m[2]),&(m[3]));\
}

/**
 *@ingroup GROUPMatrix2by2
 *@brief Prints matrix elements to the output stream.
 *
 *Prints matrix elements to the output stream.
 *
 *@param m  a pointer of type  matrix2by2_t to a 4 element vector.
 *@param out a pointer to a file.
 *
 *@descript prints the matrix  m as a 2x2 grid of elements.
 */
#define print_matrix2by2(m)\
{\
    printf("[%f, %f]\n[%f, %f]\n",m[0],m[1],m[2],m[3]);\
}

/**
 *@ingroup GROUPMatrix2by2
 *@brief Performs matrix addition, i.e.,  m =  m1 +  m2..
 *
 *Performs matrix addition, i.e.,  m =  m1 +  m2.
 *
 *@param m1 a pointer of type  matrix2by2_t to a 4 element vector.
 *@param m2 a pointer of type  matrix2by2_t to a 4 element vector.
 *@param m  a pointer of type  matrix2by2_t to a 4 element vector.
 */
#define add_matrix2by2(m1,m2,m)\
{\
    m[0] = m1[0] + m2[0];   m[1]  = m1[1] + m2[1];\
	m[2] = m1[2] + m2[2];   m[3]  = m1[3] + m2[3];\
}


/**
 *@ingroup GROUPMatrix2by2
 *@brief Performs matrix subtraction, i.e.,  m =  m1 -  m2..
 *
 *Performs matrix subtraction, i.e.,  m =  m1 -  m2.
 *
 *@param m1 a pointer of type  matrix2by2_t to a 4 element vector.
 *@param m2 a pointer of type  matrix2by2_t to a 4 element vector.
 *@param m  a pointer of type  matrix2by2_t to a 4 element vector.
 */
#define sub_matrix2by2(m1,m2,m)\
{\
    m[0] = m1[0] - m2[0];  m[1]  = m1[1] - m2[1];\
	m[2] = m1[2] - m2[2];  m[3]  = m1[3] - m2[3];\
}

/**
 *@ingroup GROUPMatrix2by2
 *@brief Multiplies a matrix by a scalar.
 *
 *Multiplies a matrix by a scalar.
 *
 *@param m1 a pointer of type  matrix2by2_t to a 4 element vector.
 *@param d  a scalar value.
 *@param m  a pointer of type  matrix2by2_t to a 4 element vector.
 */
#define multiply_scalar_matrix2by2(m1,d,m)\
{\
    m[0] = m1[0] * (d);  m[1]  = m1[1] * (d);\
	m[2] = m1[2] * (d);  m[3]  = m1[3] * (d);\
}

/**
 *@ingroup GROUPMatrix2by2
 *@brief Performs matrix multiplication, i.e.,  m =  m1 *  m2.
 *
 *Performs matrix multiplication, i.e.,  m =  m1 *  m2.
 *
 *@param m1 a pointer of type  matrix2by2_t to a 4 element vector.
 *@param m2 a pointer of type  matrix2by2_t to a 4 element vector.
 *@param m  a pointer of type  matrix2by2_t to a 4 element vector.
 *
 *@warning If  m points to the same matrix as either  m1 or  m2, then the result
 *may be incorrect.
 */
#define multiply_matrix_matrix2by2(m1,m2,m)\
{\
    m[0] = m1[0] * m2[0] + m1[1] * m2[2];\
    m[1] = m1[0] * m2[1] + m1[1] * m2[3];\
    m[2] = m1[2] * m2[0] + m1[3] * m2[2];\
    m[3] = m1[2] * m2[1] + m1[3] * m2[3];\
}

/**
 *@ingroup GROUPMatrix2by2
 *@brief Tests for matrix equality.
 *
 *Tests for matrix equality.
 *
 *@param m1 a pointer of type  matrix2by2_t to a 4 element vector.
 *@param m2 a pointer of type  matrix2by2_t to a 4 element vector.
 *@param b  a boolean variable.
 *
 *@descript sets  b to  TRUE iff every element of matrix  m1 is equal to the
 * corresponding element in matrix  m2.
 */
#define equal_matrix2by2(m1,m2,b)\
{\
    b = (m1[0] == m2[0] && m1[1] == m2[1] && m1[2] == m2[2] && m1[3] == m2[3]);\
}

/**
 *@ingroup GROUPMatrix2by2
 *@brief Copies matrix  m1 into  matrix  m, i.e.,  m = COPY(m1).
 *
 *Copies matrix  m1 into  matrix  m, i.e.,  m = COPY(m1).
 *
 *@param m1 a pointer of type  matrix2by2_t to a 4 element vector.
 *@param m  a pointer of type  matrix2by2_t to a 4 element vector.
 */
#define copy_matrix2by2(m,m1)\
{\
    m[0] = m1[0];      m[1] = m1[1];       m[2] = m1[2];    m[3] = m1[3];\	
}

/**
 *@ingroup GROUPMatrix2by2
 *@brief Copies the transpose of matrix  m1 into the matrix  m, i.e.,  m = COPY(TRANSP(m1)).
 *
 *Copies the transpose of matrix  m1 into  matrix m, i.e.,  m = COPY(TRANSP(m1)).
 *
 *@param m1 a pointer of type  matrix2by2_t to a 4 element vector.
 *@param m  a pointer of type  matrix2by2_t to a 4 element vector.
 */
#define copy_transpose_matrix2by2(m,m1)\
{\
    m[0] = m1[0];      m[1] = m1[2];       m[2] = m1[1];    m[3] = m1[0];\
}

/**
 *@ingroup GROUPMatrix2by2
 *@brief Sets every element of matrix  m to 0.
 *
 *Sets every element of matrix  m to 0.
 *
 *@param m  a pointer of type  matrix2by2_t to a 4 element vector.
 */
#define zero_matrix2by2(m)\
{\
    m[0] = m[1] = m[2] = m[3] = 0;\
}

/**
 *@ingroup GROUPMatrix2by2
 *@brief Initializes the matrix  m to the identity matrix.
 *
 *Initializes the matrix  m to the identity matrix.
 *
 *@param m  a pointer of type  matrix2by2_t to a 4 element vector.
 */
#define identity_matrix2by2(m)\
{\
    m[1] = m[2] = 0;\
    m[0] = m[3] = 1;\
}
/**
 *@ingroup GROUPMatrix2by2
 *@brief Sets the matrix  m to the transpose of itself, i.e., m = TRANSP(m).
 *
 *Sets the matrix  m to the transpose of itself.
 *
 *@param m  a pointer of type  matrix2by2_t to a 4 element vector.
 */
#define transpose_matrix2by2(m)\
{\
    double tempM3000;\
    tempM3000 = m[1];    m[1] = m[2];    m[2] = tempM3000;\
}


#define set_roty_matrix2by2(m,rad)\
{\
}
/**
 *@ingroup GROUPMatrix2by2
 *@brief Rotational matrix about the origin.
 *
 *
 *@param m   a pointer of type  matrix2by2_t to a 4 element vector.
 *@param rad a scalar value representing an angle in radians.
 *
 *@descript   the matrix  m represents the rotation by an angle of rad radians in ccw direction
 * through the origin and along the unit vector  ax.
 */
#define set_rotation_matrix2by2(m,rad)\
{\
  double sinM2000 = sinf(rad);\
  m[0] = m[3] = cosf(rad); m[1] = -sinM2000; m[2] = sinM2000;\
}

/**
 *@ingroup GROUPMatrix2by2
 *@brief Scaling matrix.
 *
 *Scaling matrix.
 *
 *@param m   a pointer of type  matrix2by2_t to a 4 element vector.
 *@param sx  a scalar value representing scaling in x-direction.
 *@param sy  a scalar value representing scaling in y-direction.
 *
 *@descript   the matrix  m represents scaling through the origin by  sx in the x-direction and
 *  sy in the y-direction. 
 */
#define set_scale_matrix2by2(m,sx,sy)\
{\
    m[1] = m[2] = 0;\
    m[0] = sx;\
    m[3] = sy;\
}

/**
 *@ingroup GROUPMatrix2by2
 *@brief Calculates the determinant.
 *
 *Calculates the determinant.
 *
 *@param m   a pointer of type  matrix2by2_t to a 4 element vector.
 *@param det an out variable of type double.
 *
 *@return   the determinant of the matrix  m.
 */
#define calc_determinant_matrix2by2(m,det)\
{\
    det = m[0]*m[3] - m[1]*m[2];
}

/**
 *@ingroup GROUPMatrix2by2
 *@brief Computes the inverse matrix, i.e.,  m = INVERSE(m1).
 *
 *Computes the inverse matrix, i.e.,  m = INVERSE(m1).
 *
 *@param m   a pointer of type  matrix2by2_t to a 4 element vector.
 *@param m1  a pointer of type  matrix2by2_t to a 4 element vector.
 *
 *@descript  the (i,j)-th entry of the inverse of  m1 is equal to ADJ(m1, i, j)/DET(m1).
 *
 *@warning If  m points to the same matrix as m1, then the result may be incorrect.
 */
#define invert_square_matrix2by2(m,m1)\
{\
    double detM2000;\
    calc_determinant_matrix2by2(m1,detM2000);\
    if( detM3000 != 0 )\
    {\
	m[0] = m1[3] / detM2000;\
	m[1] =-m1[2] / detM2000;\
	m[2] = m1[1] / detM2000;\
	m[3] = m1[0] / detM2000;\
    }\
    else\
	printf("DET = 0!!!! I cannot invert this matrix\n");\
}

//END_C_DECL

#endif
