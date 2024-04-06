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


#ifndef ___QUATERNION_H__ABCDEEDCBA_
#define ___QUATERNION_H__ABCDEEDCBA_

#include <stdio.h>
#include <stdlib.h>
#include <math.h>

#include "vector4d.h"

BEGIN_C_DECL

/** 
 *@defgroup GROUPQuaternion Fast quaternion operations.
 */

/**
 * @ingroup GROUPQuaternion
 * Defining quaternions as vector4d_t.
 */
typedef vector4d_t quaternion_t;

/**
 *@ingroup GROUPQuaternion
 *@brief Converts a 4d vector of the form (axis, angle) into a normalized quaternion.
 *
 *Converts a 4d vector of the form (axis, angle) into a normalized quaternion.
 &
 *@param o a pointer of type  quaternion_t to a vector of 4 elements.
 *
 *@warning the value of angle is in degrees.
 */
#define normalize_quaternion(o)\
{\
    double ThetaQU000 = (o[3] * M_PI) / 360.0;\
    double magnQU001  = sqrt(o[0]* o[0] + o[1]*o[1] + o[2]*o[2]);\
    if( magnQU001 == 0 )\
	magnQU001 = 1;\
    double sinNormQU002 = sin( ThetaQU000 ) / magnQU001;\
    o[0] = o[0] * sinNormQU002;\
    o[1] = o[1] * sinNormQU002;\
    o[2] = o[2] * sinNormQU002;\
    o[3] = cos( ThetaQU000 );\
}

/**
 *@ingroup GROUPQuaternion
 *@brief Creates a normalized quaternion out of 4 elements representing (axis, angle).
 *
 *Creates a normalized quaternion out of 4 elements representing (axis, angle).
 *
 *@param a  a double representing the x-coordinate of the axis vector.
 *@param b  a double representing the y-coordinate of the axis vector.
 *@param c  a double representing the z-coordinate of the axis vector.
 *@param d  a double representing the angle (degrees).
 *@param o  a pointer of type quaternion_t to a vector of 4 elements.
 *
 *@warning the value of angle is in degrees.
 */
#define set_quaternion(a,b,c,d,o)\
{\
    o[0] = a;\
    o[1] = b;\
    o[2] = c;\
    o[3] = d;\
    normalize_quaternion(o);\
}

/**
 *@ingroup GROUPQuaternion
 *@brief Reads the axis and angle from the input file and creates a normalized quaternion.
 *
 *Reads the axis and angle from the input file and creates a normalized quaternion.
 *
 *@param o  a pointer of type  quaternion_t to a vector of 4 elements.
 *@param in a pointer to a file.
 *
 *@warning the value of angle is in degrees.
 */
#define read_quaternion(o,in)\
{\
    fscanf(in, "%lf %lf %lf %lf", &(o[0]), &(o[1]), &(o[2]), &(o[3]));\
    normalize_quaternion(o);\
}

/**
 *@ingroup GROUPQuaternion
 *@brief Performs quaternion multiplication, i.e., o = o1 * o2.
 *
 *Performs quaternion multiplication, i.e., o = o1 * o2.
 *
 *@param o1 a pointer of type  quaternion_t to a vector of 4 elements.
 *@param o2 a pointer of type  quaternion_t to a vector of 4 elements.
 *@param o  a pointer of type  quaternion_t to a vector of 4 elements.
 */
#define multiply_quaternion(o1,o2,o)\
{\
    o[0] = + o1[0]*o2[3] + o1[1]*o2[2] - o1[2]*o2[1] + o1[3]*o2[0];\
    o[1] = - o1[0]*o2[2] + o1[1]*o2[3] + o1[2]*o2[0] + o1[3]*o2[1];\
    o[2] = + o1[0]*o2[1] - o1[1]*o2[0] + o1[2]*o2[3] + o1[3]*o2[2];\
    o[3] = - o1[0]*o2[0] - o1[1]*o2[1] - o1[2]*o2[2] + o1[3]*o2[3];\
}

/**
 *@ingroup GROUPQuaternion
 *@brief Computes the inverse of the quaternion, o = INVERSE(o).
 *
 *Computes the inverse of the quaternion, o = INVERSE(o).
 *
 *@param o  a pointer of type  quaternion_t to a vector of 4 elements.
 */
#define inverse_quaternion(o)\
{\
    o[3] = -(o[3]);\
}

/**
 *@ingroup GROUPQuaternion
 *@brief Computes the quaternion o = INVSERSE(o1) * o2.
 *
 *Computes the quaternion o = INVSERSE(o1) * o2.
 *
 *@param o1 a pointer of type  quaternion_t to a vector of 4 elements.
 *@param o2 a pointer of type  quaternion_t to a vector of 4 elements.
 *@param o  a pointer of type  quaternion_t to a vector of 4 elements.
 */
#define calc_transition_quaternion(o1, o2, o)\
{\
    o[0] = + o1[0]*(-o2[3]) + o1[1]*o2[2]    - o1[2]*o2[1]    + o1[3]*o2[0];\
    o[1] = - o1[0]*o2[2]    + o1[1]*(-o2[3]) + o1[2]*o2[0]    + o1[3]*o2[1];\
    o[2] = + o1[0]*o2[1]    - o1[1]*o2[0]    + o1[2]*(-o2[3]) + o1[3]*o2[2];\
    o[3] = - o1[0]*o2[0]    - o1[1]*o2[1]    - o1[2]*o2[2]    + o1[3]*(-o2[3]);\
}

/**
 *@ingroup GROUPQuaternion
 *@brief Linearly interpolates quaternions o1 and o2, i.e., o = (1-f)*o1 + f * o2.
 *
 *Linearly interpolates quaternions o1 and o2, i.e., o = (1-f)*o1 + f * o2.
 *
 *@param o1 a pointer of type  quaternion_t to a vector of 4 elements.
 *@param o2 a pointer of type  quaternion_t to a vector of 4 elements.
 *@param f  a double representing the interpolation factor.
 *@param o  a pointer of type  quaternion_t to a vector of 4 elements.
 */
#define interpolate_quaternion(o1,o2,f,o)\
{\
      double wmegaIQ, dot_pIQ, a_factorIQ, b_factorIQ, sinWIQ;\
      dot_vector4d( o1, o2, dot_pIQ );\
      wmegaIQ = acos(  dot_pIQ );\
      sinWIQ = sin(wmegaIQ);\
      a_factorIQ = sin(( 1.0 - f ) * wmegaIQ)/sinWIQ;\
      b_factorIQ = sin( wmegaIQ * f)/sinWIQ;\
      o[0] = o1[0] * a_factorIQ + o2[0] * b_factorIQ;\
      o[1] = o1[1] * a_factorIQ + o2[1] * b_factorIQ;\
      o[2] = o1[2] * a_factorIQ + o2[2] * b_factorIQ;\
      o[3] = o1[3] * a_factorIQ + o2[3] * b_factorIQ;\
}

/**
 *@ingroup GROUPQuaternion
 *@brief Linearly interpolates quaternions o1 and o2, i.e., o = (1-f)*o1 + f * o2.
 *
 *Linearly interpolates quaternions o1 and o2, i.e., o = (1-f)*o1 + f * o2.
 *
 *@param o1      a pointer of type  quaternion_t to a vector of 4 elements.
 *@param o2      a pointer of type  quaternion_t to a vector of 4 elements.
 *@param f       a double representing the interpolation factor.
 *@param wmegaIQ a double representing the angle between the two quaternions.
 *@param sinWIQ  a double representing sin(wmegaIQ)ls

 *@param o       a pointer of type  quaternion_t to a vector of 4 elements.
 */
#define super_interpolate_quaternion(o1,o2,f,wmegaIQ,sinWIQ,o)\
{\
      double a_factorIQ, b_factorIQ;\
      a_factorIQ = sin(( 1.0 - f ) * wmegaIQ)/sinWIQ;\
      b_factorIQ = sin( wmegaIQ * f)/sinWIQ;\
      o[0] = o1[0] * a_factorIQ + o2[0] * b_factorIQ;\
      o[1] = o1[1] * a_factorIQ + o2[1] * b_factorIQ;\
      o[2] = o1[2] * a_factorIQ + o2[2] * b_factorIQ;\
      o[3] = o1[3] * a_factorIQ + o2[3] * b_factorIQ;\
}

/**
 *@ingroup GROUPQuaternion
 *@brief Computes the 3x3 matrix that represents the same transformation as the quaternion.
 *
 *Computes the 3x3 matrix that represents the same transformation as the quaternion.
 *
 *@param m  a pointer of type  matrix3by3_t to a vector of 9 elements.
 *@param o  a pointer of type  quaternion_t to a vector of 4 elements.
 */
#define from_quaternion_to_matrix3by3(m,o)\
{\
    m[0] = 1 - 2*o[1]*o[1] - 2*o[2]*o[2];\
    m[1] = 2*o[0]*o[1] - 2*o[2]*o[3];\
    m[2] = 2*o[0]*o[2] + 2*o[1]*o[3];\
    m[3] = 2*o[0]*o[1] + 2*o[2]*o[3];\
    m[4] = 1 - 2*o[0]*o[0] - 2*o[2]*o[2];\
    m[5] = 2*o[1]*o[2] - 2*o[0]*o[3];\
    m[6] = 2*o[0]*o[2] - 2*o[1]*o[3];\
    m[7] = 2*o[1]*o[2] + 2*o[0]*o[3];\
    m[8] = 1 - 2*o[0]*o[0] - 2*o[1]*o[1];\
}

/**
 *@ingroup GROUPQuaternion
 *@brief Computes the 4x4 matrix that represents the same transformation as the quaternion.
 *
 *Computes the 4x4 matrix that represents the same transformation as the quaternion.
 *
 *@param m  a pointer of type  matrix4by4_t to a vector of 16 elements.
 *@param o  a pointer of type  quaternion_t to a vector of 4 elements.
 */
#define from_quaternion_to_matrix4by4(m,o)\
{\
    m[0] = 1 - 2*o[1]*o[1] - 2*o[2]*o[2];\
    m[1] = 2*o[0]*o[1] - 2*o[2]*o[3];\
    m[2] = 2*o[0]*o[2] + 2*o[1]*o[3];\
    m[3] = 0.0;\
    m[4] = 2*o[0]*o[1] + 2*o[2]*o[3];\
    m[5] = 1 - 2*o[0]*o[0] - 2*o[2]*o[2];\
    m[6] = 2*o[1]*o[2] - 2*o[0]*o[3];\
    m[7] = 0.0;\
    m[8] = 2*o[0]*o[2] - 2*o[1]*o[3];\
    m[9] = 2*o[1]*o[2] + 2*o[0]*o[3];\
    m[10] = 1 - 2*o[0]*o[0] - 2*o[1]*o[1];\
    m[11] = 0.0;\
    m[12] = m[13] = m[14] = 0.0;\
    m[15] = 1.0;\
}

END_C_DECL

#endif
