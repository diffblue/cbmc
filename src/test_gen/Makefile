SRC = java_test_case_generator.cpp java_test_source_factory.cpp

INCLUDES= -I ..

include ../config.inc
include ../common

CLEANFILES = test_gen$(LIBEXT)

all: test_gen$(LIBEXT)

###############################################################################

test_gen$(LIBEXT): $(OBJ)
	$(LINKLIB)

