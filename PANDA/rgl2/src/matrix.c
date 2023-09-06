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


#include "matrix.h"


void lu_backsub_matrix(double** a, int n, int* indx, double* b);
int  lu_decomp_matrix(double** a, int n, int* indx, double* d);

void transpose_matrix( matrix_t m )
{
    int lines    = get_rows_matrix(m);
    int cols     = get_cols_matrix(m);
    int i = 0, j = 0;
    if( lines == cols )
    {
	double temp;
	
	for(i=0; i<lines; i++ )
	    for(j=i+1; j<cols; j++ )
	    {
		temp = m[i*cols + j];
		m[i*cols + j] = m[j*cols + i];
		m[j*cols + i] = temp;
	    }
    }
    else
    {
        matrix_t temp;
        alloc_matrix(temp, cols, lines, double);
        copy_transpose_matrix(temp, m);
        free_matrix(m);
        m = temp;
    }
}

void lu_backsub_matrix(double** a, int n, int* indx, double* b)
{
    double sum;
    int ii = -1;
    
    int i = 0, ip = 0, j = 0;
     
    for(i=0; i<n; i++) 
    {
	ip = indx[i];
	sum = b[ip];
	b[ip] = b[i];
	if (ii != -1 ) 
	    for (j=ii; j<=i-1; j++ ) 
		sum -= a[i][j]*b[j];
	else if (sum) 
	    ii = i;
	b[i] = sum;
    }

    for (i=n-1; i>=0; i--)
    {
	sum = b[i];
	for (j=i+1; j<n; j++ )
	    sum -= a[i][j]*b[j];
	b[i] = sum/a[i][i];
    }
}

int lu_decomp_matrix(double** a, int n, int* indx, double* d)
{
    int imax=0;
    double big, dum, sum, temp;
    double *vv = (double*)malloc(n*sizeof(double));
    
    int i = 0, j = 0, k = 0, x = 0, y = 0;
    *d = 1.0;

    for(i=0; i < n; i++)
    {
	big = 0.0;
	for(j=0; j < n; j++)
	    if((temp = fabs(a[i][j])) > big)
		big = temp;
	if (big == 0.0)
	{
	    printf("Matrix:: singular matrix in luDecomp::\n");
	    for(x=0; x<n; x++ )
	    {
		for( y=0; y<n; y++ )
		    printf("%f  ",a[x][y]);
		printf("\n");
	    }
	    return 0;
	}
	vv[i] = 1.0/big;
    }

    for(j=0; j < n; j++)
    {
	for(i=0; i < j; i++)
	{
	    sum = a[i][j];
	    for(k=0; k < i; k++)
		sum -= a[i][k]*a[k][j];
	    a[i][j] = sum;
	}
	big = 0.0;
	for(i=j; i < n; i++)
	{
	    sum = a[i][j];
	    for(k=0; k < j; k++)
		sum -=a[i][k]*a[k][j];
	    a[i][j] = sum;
	    if((dum = vv[i]*fabs(sum)) >= big)
	    {
		big = dum;
		imax = i;
	    }
	}
	if(j != imax)
	{
	    for(k=0; k < n; k++)
	    {
		dum = a[imax][k];
		a[imax][k] = a[j][k];
		a[j][k] = dum;
	    }
	    *d = -(*d);
	    vv[imax] = vv[j];
	}
	indx[j] = imax;
	if (a[j][j] == 0.0)
	    a[j][j] = TINY;
	if (j != n-1)
	{
	    dum = 1.0/(a[j][j]);
	    for(i=j+1; i < n; i++)
		a[i][j] *= dum;
	}
    }
    free( vv );
    return 1;
}

void invert_square_matrix(matrix_t m, matrix_t m1 )
{
    int lines = get_rows_matrix(m);
    int cols  = get_cols_matrix(m);
  
   
    double d;
    int*     indx = (int*)malloc(lines*sizeof(int));
    double*  col  = (double*)malloc(lines*sizeof(double));
    double** mat  = (double**)malloc(lines*sizeof(double*));

    int i = 0, j = 0;
    for( i=0; i<lines; i++ )
    {
	mat[i] = (double*)malloc(cols*sizeof(double));
	for( j=0; j<cols; j++ )
	    mat[i][j] = m1[i * cols + j];
    }

  
    lu_decomp_matrix(mat, lines, indx, &d);
    
    for(j=0; j < lines; j++)
    {
	for(i=0; i < lines; i++)
	    col[i] = 0.0;
	col[j] = 1.0;
	lu_backsub_matrix(mat, lines, indx, col);
	for(i=0; i < lines; i++ )
	    m[i * cols + j] = col[i];
    }

    free( col );
    free( indx );
    for( j=0; j<lines; j++ )
	free( mat[j] );
    free( mat );
} 
  

void pseudo_inverse_matrix( matrix_t m, matrix_t m1 )
{
    int lines = get_rows_matrix(m1);
    int cols  = get_cols_matrix(m1);

    matrix_t transp, temp;

    if( lines == cols )
	invert_square_matrix(m,m1);
    else 
    {


	if( lines > cols )
	{
	    alloc_matrix( transp, cols, lines, double );
	    alloc_matrix( temp, cols, cols, double );

	    copy_transpose_matrix( transp, m1 );
	    multiply_matrix_matrix( transp, m1, temp );
	    invert_square_matrix(temp,temp);
	    multiply_matrix_matrix(temp,transp,m);
	}
	else
	{
	    alloc_matrix( transp, cols, lines, double );
	    alloc_matrix( temp, lines, lines, double );

	    copy_transpose_matrix( transp, m1 );
	    multiply_matrix_matrix( m1, transp, temp );
	    invert_square_matrix(temp,temp);
	    multiply_matrix_matrix(transp,temp,m);
	}

	free_matrix(transp);
	free_matrix(temp);
    }
}

void sr_inverse_matrix( matrix_t m1, matrix_t m2, double *w0 )
{
}

