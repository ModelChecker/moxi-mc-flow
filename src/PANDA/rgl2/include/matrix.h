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


#ifndef ___MATRIX_H__ABCDEEDCBA_
#define ___MATRIX_H__ABCDEEDCBA_

#include <stdio.h>
#include <stdlib.h>
#include <math.h>


//BEGIN_C_DECL

#define TINY            .000000001

/** 
 *@defgroup GROUPMatrix Fast matrix operations.
 */

/**
 * @ingroup GROUPMatrix
 * Defining matrices as pointers to  double.
 */
typedef double * matrix_t;

/**
 *@ingroup GROUPMatrix
 *@brief Index where the number of rows is stored.
 *
 * Index where the number of rows is stored.
 */
#define MATRIX_ROW_INDEX -2

/**
 *@ingroup GROUPMatrix
 *@brief Index where the number of columns is stored.
 *
 *Index where the number of columns is stored.
 */
#define MATRIX_COL_INDEX -1

/**
 *@ingroup GROUPMatrix
 *@brief Offset from the beginning of the pointer.
 *
 *Offset from the beginning of the pointer.
 */
#define MATRIX_ELEM_INDEX 2

/**
 *@ingroup GROUPMatrix
 *@brief Returns the first address of the pointer.
 *
 *Returns the first address of the pointer.
 *
 *@param m a pointer of type  matrix_t to a vector of elements.
 */
#define get_address_matrix(m)\
  (m - MATRIX_ELEM_INDEX)


/**
 *@ingroup GROUPMatrix
 *@brief Advance matrix pointer to point to the beginning of the elements.
 *
 *Advance matrix pointer to point to the beginning of the elements.
 *@param m a pointer of type  matrix_t to a vector of elements.
 */
#define advance_matrix(m)\
{\
  m = m + MATRIX_ELEM_INDEX;\
}
 
/**
 *@ingroup GROUPMatrix
 *@brief Access number of rows.
 *
 *Access number of rows.
 *
 *@param m a pointer of type  matrix_t to a vector of elements.
 */
#define get_rows_matrix(m)\
((int) (m[MATRIX_ROW_INDEX]))

/**
 *@ingroup GROUPMatrix
 *@brief Access number of columns.
 *
 *Access number of columns.
 *
 *@param m a pointer of type  matrix_t to a vector of elements.
 */
#define get_cols_matrix(m)\
((int) (m[MATRIX_COL_INDEX]))

/**
 *@ingroup GROUPMatrix
 *@brief Calculates the dimension of the matrix as the number of the elements.
 *
 *Calculates the dimension of the matrix as the number of elements.
 *
 *@param m a pointer of type  matrix_t to a vector of elements.
 *
 *@return number of elements.
 */
#define get_dim_matrix(m)\
((get_rows_matrix(m))*(get_cols_matrix(m)))

/**
 *@ingroup GROUPMatrix
 *@brief Calculates the index of the element in row  r and column c.
 *
 *Calculates the index of the element in row  r and column c.
 *
 *@param m a pointer of type  matrix_t to a vector of elements.
 *@param r an integer representing row index.
 *@param c an integer representing column index.
 */
#define get_index_matrix(m, r, c)\
((r)*(get_cols_matrix(m)) + (c))

/**
 *@ingroup GROUPMatrix4by4
 *@brief Access matrix element with index i.
 *
 *Access matrix element with index i.
 *
 *@param m a pointer of type  matrix_t to a vector of elements.
 *@param i an integer in the range 0...DIM-1 representing the index.
 *
 *@returns the element in row r and column c of matrix m, where
 * i = NR_COLS x r + c.
 */
#define get_elem_matrix(m, i)\
(m[i])

/**
 *@ingroup GROUPMatrix
 *@brief Set matrix element, i.e.,  m[i] = v.
 *
 *Set matrix element, i.e., m[i] = v.
 *
 *@param m a pointer of type  matrix_t to a vector of elements.
 *@param i an integer in the range 0...DIM-1 representing the index.
 *
 *@descript sets the value of the element in row r and column c of matrix m to v,
 *where i = NR_COLS x r + c.
 */
#define set_elem_matrix(m, i, v)\
{\
    m[i] = v;\
}

/**
 *@ingroup GROUPMatrix
 *@brief Allocate memory.
 *
 *Allocate memory.
 *
 *@param m a pointer of type  matrix_t to which no memory has been allocated.
 *@param t element type, i.e.,  double,  float,  int, etc.
 *@param r an integer representing the number of rows.
 *@param c an integer representing the number of columns.
 *
 *@descript allocates to m a contigous block of r x c elements of type t.
 */
#define alloc_matrix(m,r,c,t)\
{\
    m = (t*)malloc(((r)*(c) + 2)*sizeof(t));\
    advance_matrix(m);\
    set_elem_matrix(m, MATRIX_ROW_INDEX, r);\
    set_elem_matrix(m, MATRIX_COL_INDEX, c);\
}

/**
 *@ingroup GROUPMatrix
 *@brief Free memory.
 *
 *Free memory.
 *
 *@param m  a pointer of type  matrix_t to a vector of elements.
 *
 *@descript frees the memory allocated to m.
 */
#define free_matrix(m)\
{\
    if(m) {free(get_address_matrix(m));}\
}

/**
 *@ingroup GROUPMatrix
 *@brief Reads matrix elements from a file stream.
 *
 *Reads matrix elements from a file stream.
 *
 *@param m  a pointer of type  matrix_t to a vector of elements.
 *@param in a pointer to a file.
 *
 *@descript reads the elements of the matrix m from the file to which in points to.
 */
#define read_matrix(m,in)\
{\
    int dimMA000 = get_dim_matrix(m);\
    int iMA000=0;\
    for(iMA000=0; iMA000<dimMA000; iMA000++ )\
            fscanf(in,"%lf",&((m)[iMA000]));\
}

/**
 *@ingroup GROUPMatrix
 *@brief Prints matrix elements to the standard output device.
 *
 *Prints matrix elements to the standard output device.
 *
 *@param m  a pointer of type  matrix_t to a vector of elements.
 *
 *@descript prints the matrix m as a NR_ROWS x NR_COLS grid of elements.
 */
#define print_matrix(m)\
{\
    int rMA000   = get_rows_matrix(m);\
    int cMA000   = get_cols_matrix(m);\
    int iMA000=0, jMA001=0;\
    printf("(%d x %d):\n", rMA000, cMA000);\
    for (iMA000=0; iMA000<rMA000; iMA000++)\
    {\
	printf("[");\
	for (jMA001=0; jMA001<cMA000; jMA001++)\
	    printf("%f, ", m[iMA000*cMA000 + jMA001]);\
	printf("]\n");\
    }\
}

/**
 *@ingroup GROUPMatrix
 *@brief Performs matrix addition, i.e., m = m1 + m2.
 *
 *Performs matrix addition, i.e., m = m1 + m2.
 *@param m  a pointer of type  matrix_t to a vector of elements.
 *@param m1 a pointer of type  matrix_t to a vector of elements.
 *@param m2 a pointer of type  matrix_t to a vector of elements.
 */
#define add_matrix(m1,m2,m)\
{\
    int dimMA000 = get_dim_matrix(m);\
    int iMA000=0;\
    for(iMA000=0; iMA000<dimMA000; iMA000++)\
        m[iMA000] = m1[iMA000] + m2[iMA000];\
}

/**
 *@ingroup GROUPMatrix
 *@brief Performs matrix subtraction, i.e.,  m =  m1 -  m2..
 *
 *Performs matrix subtraction, i.e.,  m =  m1 -  m2.
 *
 *@param m  a pointer of type  matrix_t to a vector of elements.
 *@param m1 a pointer of type  matrix_t to a vector of elements.
 *@param m2 a pointer of type  matrix_t to a vector of elements.
 */
#define sub_matrix(m1,m2,m)\
{\
    int dimMA000 = get_dim_matrix(m);\
    int iMA000=0;\
    for(iMA000=0; iMA000<dimMA000; iMA000++)\
        m[iMA000] = m1[iMA000] - m2[iMA000];\
}

/**
 *@ingroup GROUPMatrix
 *@brief Multiplies a matrix by a scalar.
 *
 *Multiplies a matrix by a scalar.
 *
 *@param m1 a pointer of type  matrix_t to a vector of elements.
 *@param d  a scalar value.
 *@param m  a pointer of type  matrix_t to a vector of elements.
 */
#define multiply_scalar_matrix(m1,d,m)\
{\
    int dimMA000 = get_dim_matrix(m);\
    int iMA000=0;\
    for(iMA000=0; iMA000<dimMA000; iMA000++)\
        m[iMA000] = m1[iMA000] * d;\
}

/**
 *@ingroup GROUPMatrix
 *@brief Performs matrix multiplication, i.e., m = m1 * m2.
 *
 *Performs matrix multiplication, i.e., m = m1 * m2.
 *
 *@param m  a pointer of type  matrix_t to a vector of elements.
 *@param m1 a pointer of type  matrix_t to a vector of elements.
 *@param m2 a pointer of type  matrix_t to a vector of elements.
 *
 *@warning If m points to the same matrix as either m1 or m2, then the result
 *may be incorrect.
 */
#define multiply_matrix_matrix(m1,m2,m)\
{\
    int r1MA000 = get_rows_matrix(m1);\
    int c1MA000 = get_cols_matrix(m1);\
    int c2MA000 = get_cols_matrix(m2);\
    int indexMA000 = 0;\
    int iMA000=0,jMA001=0,kMA002=0;\
    for(iMA000=0; iMA000<r1MA000; iMA000++)\
     for(jMA001=0; jMA001<c2MA000; jMA001++)\
     {\
         indexMA000 = get_index_matrix(m, iMA000, jMA001);\
         m[indexMA000] = 0;\
          for(kMA002=0; kMA002<c1MA000; kMA002++)\
           m[indexMA000] += (m1[get_index_matrix(m1, iMA000, kMA002)] * m2[get_index_matrix(m2, kMA002, jMA001)]);\
    }\
}

/**
 *@ingroup GROUPMatrix
 *@brief Tests for matrix equality.
 *
 *Tests for matrix equality.
 *
 *@param m1 a pointer of type  matrix_t to a vector of elements.
 *@param m2 a pointer of type  matrix_t to a vector of elements.
 *@param b  a boolean variable.
 *
 *@descript sets b to TRUE iff every element of matrix m1 is equal to the
 *corresponding element in matrix m2.
 */
#define equal_matrix(m1,m2,b)\
{\
    int dim1MA000 = get_dim_matrix(m1);\
    int dim2MA000 = get_dim_matrix(m2);\
    int iMA000=0;\
    b = dim1MA000 == dim2MA000;\
    for(iMA000=0; iMA000<dim1MA000 && b; iMA000++)\
        b = m1[iMA000] == m2[iMA000];\
}

/**
 *@ingroup GROUPMatrix
 *@brief Copies matrix m1 into matrix m, i.e., m = COPY(m1).
 *
 *Copies matrix m1 into matrix m, i.e.,  m = COPY(m1).
 *
 *@param m  a pointer of type  matrix_t to a vector of elements.
 *@param m1 a pointer of type  matrix_t to a vector of elements.
 */
#define copy_matrix(m,m1)\
{\
    int dimMA000 = get_dim_matrix(m);\
    int iMA000=0;\
    for(iMA000=0; iMA000<dimMA000; iMA000++)\
        m[iMA000] = m1[iMA000];\
}

/**
 *@ingroup GROUPMatrix
 *@brief Copies the transpose of matrix m1 into the matrix m, i.e., m = COPY(TRANSP(m1)).
 *
 *Copies the transpose of matrix  m1 into matrix m, i.e., m = COPY(TRANSP(m1)).
 *
 *@param m a pointer of type  matrix_t to a vector of elements.
 *@param m1 a pointer of type  matrix_t to a vector of elements. 
 */
#define copy_transpose_matrix(m,m1)\
{\
     int rMA000  = get_rows_matrix(m);\
     int cMA000  = get_cols_matrix(m);\
     int iMA000=0, jMA001=0;\
     for(iMA000=0; iMA000<rMA000; iMA000++ )\
      for(jMA001=0; jMA001<cMA000; jMA001++ )\
       m[iMA000*cMA000 + jMA001] = m1[jMA001*rMA000 + iMA000];\
}

/**
 *@ingroup GROUPMatrix
 *@brief Sets every element of matrix  m to 0.
 *
 *Sets every element of matrix  m to 0.
 *
 *@param m a pointer of type  matrix_t to a vector of elements.
 */
#define zero_matrix(m)\
{\
    int dimMA000 = get_dim_matrix(m);\
    int iMA000=0;\
    for(iMA000=0; iMA000<dimMA000; iMA000++)\
        m[iMA000] = 0;\
}

/**
 *@ingroup GROUPMatrix
 *@brief Initializes the matrix  m to the identity matrix.
 *
 *Initializes the matrix  m to the identity matrix.
 *
 *@param m a pointer of type  matrix_t to a vector of elements.
 */
#define identity_matrix(m)\
{\
    int rMA000 = get_rows_matrix(m);\
    int cMA000 = get_cols_matrix(m);\
    int iMA000=0, jMA001=0;\
     for(iMA000=0; iMA000<rMA000; iMA000++ )\
	for(jMA001=0; jMA001<cMA000; jMA001++ )\
	    m[iMA000*cMA000 + jMA001] = (iMA000 == jMA001);\
}

/**
 *@ingroup GROUPMatrix
 *@brief Sets the matrix  m to the transpose of itself, i.e., m = TRANSP(m).
 *
 *Sets the matrix  m to the transpose of itself,  i.e., m = TRANSP(m).
 *
 *@param m a pointer of type  matrix_t to a vector of elements.
 */
void transpose_matrix( matrix_t m );

/**
 *@ingroup GROUPMatrix
 *@brief Computes the inverse matrix, i.e.,  m = INVERSE(m1).
 *
 *Computes the inverse matrix, i.e.,  m = INVERSE(m1).
 *
 *@param m a pointer of type  matrix_t to a vector of elements.
 *@param m1a pointer of type  matrix_t to a vector of elements.
 *
 *@descript  the (i,j)-th entry of the inverse of  m1 is equal to
 *  ADJ(m1, i, j)/DET(m1).
 */
void invert_square_matrix( matrix_t m, matrix_t m1 );

/**
 *@ingroup GROUPMatrix
 *@brief Computes the pseudo-inverse matrix, i.e.,  m = PSEUDO-INVERSE(m1).
 *
 *Computes the pseudo-inverse matrix, i.e.,  m = PSEUDO-INVERSE(m1).
 *
 *@param m  a pointer of type  matrix_t to a vector of elements.
 *@param m1 a pointer of type  matrix_t to a vector of elements.
 */
void pseudo_inverse_matrix( matrix_t m, matrix_t m1 );

/**
 *@ingroup GROUPMatrix
 *@brief Computes the sr-inverse matrix, i.e.,  m = SR-INVERSE(m1).
 *
 *Computes the sr-inverse matrix, i.e.,  m = SR-INVERSE(m1).
 *
 *@param m  a pointer of type  matrix_t to a vector of elements.
 *@param m1 a pointer of type  matrix_t to a vector of elements.
 */
void sr_inverse_matrix( matrix_t m1, matrix_t m2, double* w0 );


//END_C_DECL

#endif
