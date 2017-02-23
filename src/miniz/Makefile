SRC = miniz.cpp

INCLUDES= -I ..

include ../config.inc
include ../common

CLEANFILES = miniz$(LIBEXT)

all: miniz$(LIBEXT)

###############################################################################

miniz$(LIBEXT): $(OBJ)
	$(LINKLIB)
