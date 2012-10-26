SRC = float_utils.cpp

INCLUDES= -I .. -I ../util

include ../config.inc
include ../common

LIBS = ../solvers/solvers$(LIBEXT) \
       ../ansi-c/ansi-c$(LIBEXT) \
       ../linking/linking$(LIBEXT) \
			 ../util/util$(LIBEXT) \
			 ../big-int/bigint$(OBJEXT)

CLEANFILES = floatbv$(LIBEXT) float_utils_test$(EXEEXT)

all: floatbv$(LIBEXT)

###############################################################################

floatbv$(LIBEXT): $(OBJ)
	$(LINKLIB)

float_utils_test$(EXEEXT): float_utils_test$(OBJEXT)
	$(LINKBIN)

