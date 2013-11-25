include ../config.inc
include ../common

SRC = bigint-func.cc bigint.cc
PRG = test-bigint$(EXEEXT)
CLEANFILES = $(PRG) big-int$(LIBEXT) bigint-test$(OBJEXT) bigint-test.d

all : $(PRG) big-int$(LIBEXT)

big-int$(LIBEXT): $(OBJ)
	$(LINKLIB)

$(PRG): $(OBJ) bigint-test$(OBJEXT)
	$(LINKBIN)

