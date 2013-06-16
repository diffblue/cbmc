include ../config.inc
include ../common

SRC = bigint-func.cc bigint.cc
PRG = test-bigint$(EXEEXT)
CLEANFILES = $(PRG)

all : $(PRG)

$(PRG): $(OBJ) bigint-test$(OBJEXT)
	$(LINKBIN)

