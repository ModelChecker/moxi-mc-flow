CC = gcc
CXX = g++

INCLUDES =  include 
CXXINCLUDES = 

CFLAGS = -Wall $(INCLUDES:%=-I%) -O3 -g
CXXFLAGS = $(CFLAGS) $(CXXINCLUDES:%=-I%) -O3 -g
LFLAGS = -lm 

MODULES_CPP =

#KYR added gatorade:
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
	heuristics\
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

MODULES = $(MODULES_C) $(MODULES_CPP)

OBJS = $(MODULES:%=objs/%.o)

CFILES = $(MODULES_C:%=%.c)
CPPFILES = $(MODULES_CPP:%=%.cpp)

PROGRAMS =\
	serial_test\
	part_test\
	librgl.a

all: depend $(PROGRAMS)

objs: $(OBJS)

debug: CFLAGS := $(CFLAGS) -g3
debug: all 

profile: CFLAGS := $(CFLAGS) -pg -O 
profile: all 

opt: CFLAGS := $(CFLAGS) -O6 -DNDEBUG
opt: all 

depend:
	cd src; makedepend -pobjs/ -- -DNDEBUG -I/usr/include/ -I/usr/lib/gcc-lib/i586-suse-linux/3.3.5/include -I/usr/lib/gcc/i586-suse-linux/4.1.2/include -I/usr/include/linux $(INCLUDES:%=-I$(PWD)/%) \
$(CXXINCLUDES:%=-I$(PWD)/%) -- -f ../makefile.deps $(CFILES) $(CPPFILES)

#doc:
#	doxygen rgl.dox

clean:
	cp makefile.deps.clean makefile.deps; \rm -f objs/*.o; rm -f include/*~ src/*~ *~

objs/%.o: src/%.c
	$(CC) -c $(CFLAGS) $< -o $@

objs/%.o: src/%.cpp
	$(CXX) -c $(CXXFLAGS) $< -o $@

%: $(OBJS) objs/%.o 
	$(CXX) $(CFLAGS) $^ $(LFLAGS) -o $@

librgl.a: $(OBJS)
	ar rv $@ $?
	ranlib $@


#KYR added next line:
test: 
	${CC} ${LDFLAGS} $^ ${LDLIBS}  -o $@	



include makefile.deps
# DO NOT DELETE