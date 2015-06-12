SRC = bmc_verification_oracle.cpp ga_learning_algorithm.cpp

INCLUDES= -I ..

include ../config.inc
include ../common

CLEANFILES = cegis$(LIBEXT)

all: cegis$(LIBEXT)

###############################################################################

cegis$(LIBEXT): $(OBJ)
	$(LINKLIB)

