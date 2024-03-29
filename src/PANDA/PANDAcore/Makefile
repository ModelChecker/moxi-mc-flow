# Note: This needs to be fixed to make inside rgl2 too, if necessary

CPPFLAGS= $(INCLUDES:%=-I%)
LDFLAGS = $(LIBRARIES:%=-L%)
LDLIBS	= -lrgl $(USED_TOOLS:%=-l%)

MAIN_DIR 	= ../
RGL_DIR		= $(MAIN_DIR)rgl2/include
RGL_LIB		= $(MAIN_DIR)rgl2
RGL_OBJ		= $(MAIN_DIR)rgl2/objs

INCLUDES	= $(RGL_DIR) $(RGL_OBJ)
LIBRARIES	= $(RGL_LIB)

MODULES_C =\
	astar\
	bheap\
	conf\
	fbheap\
	fast_union\
	graph\
	graphalg\
	graphreachable\
	graphtriangulation\
	kdtree\
	knn\
	kpartition\
	lexset\
	matrix\
	prime\
	random\
	set\
	setop\
	serial\
	serial_ds

MY_MODULES =\
	KItem\
	KList\
	PANDA\
	lex.yy\
	y.tab

OBJS = $(MODULES_C:%=${RGL_OBJ}/%.o)
MY_OBJS = $(MY_MODULES:%=%.o)

PANDA: lex yacc
	g++ -c ${CPPFLAGS} lex.yy.c y.tab.c KItem.cc KList.cc PANDA.cpp 
	g++ ${CPPFLAGS} ${LDFLAGS} ${LDLIBS} ${OBJS} ${MY_OBJS} -lfl -o PANDA

lex:
	lex lexLTL.l

yacc:
	yacc -d yaccLTL.y

parser: lex yacc
	g++ lex.yy.c y.tab.c parsetest.cc -o parser -lfl

clean:
	rm ./*.o
