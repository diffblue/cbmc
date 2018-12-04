include ../config.inc
include ../common

SRC = bigint-func.cc bigint.cc
CLEANFILES = big-int$(LIBEXT)

all: big-int$(LIBEXT)

big-int$(LIBEXT): $(OBJ)
	$(LINKLIB)
