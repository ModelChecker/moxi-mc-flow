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


#if !defined(SCENE_H)
#define SCENE_H

#include "robot3d.h"
#include "Collision3d.hpp"
#include "illumination.h"

#define DISTANCE_THRESH		0.1

BEGIN_C_DECL

typedef struct 
{
    illumination_t* illum;
    object_t**      obstacles;
    int numObstacles;
    robot_t**       robots;
    int numRobots;

    collision_t*    collision;
} scene3d_t;

#define alloc_scene3d(s)\
{\
    s = (scene3d_t*)malloc(sizeof(scene3d_t));\
    s->illum = NULL;\
    s->obstacles = NULL;\
    s->robots = NULL;\
    s->collision = NULL;\
    s->numObstacles = 0;\
    s->numRobots = 0;\
}

#define free_scene3d(s)\
{\
    if( s->illum != NULL )\
	free_illumination( s->illum );\
    if( s->obstacles != NULL )\
    {\
	for( int iSE01=0; iSE01<s->numObstacles; iSE01++ )\
	    free_object( s->obstacles[iSE01] );\
	free( s->obstacles );\
    }\
    if( s->robots != NULL )\
    {\
	for( int iSE01=0; iSE01<s->numRobots; iSE01++ )\
	    free_robot( s->robots[iSE01] );\
	free( s->robots );\
    }\
    if( s->collision != NULL )\
	free_collision( s->collision );\
    free(s);\
}

#define render_scene3d(s)\
{\
    render_illumination(s->illum);\
    for( int iSE02 = 0; iSE02<s->numObstacles; iSE02++ )\
	render_object( s->obstacles[iSE02] );\
    for( int iSE02 = 0; iSE02<s->numRobots; iSE02++ )\
	render_robot( s->robots[iSE02] );\
}    

#define update_robot_position( s,rId, conf  )\
{\
    set_robot_config_collision( s->collision, s->robots[rId]->robot_id, conf );\
}

#define check_collision_scene3d(s,b)\
{\
    check_collision(s->collision,b);\
}

void read_scene3d( scene3d_t* s, FILE* fp );
double calc_distance( scene3d_t* s, config_t* st, config_t* g );

END_C_DECL

#endif 
