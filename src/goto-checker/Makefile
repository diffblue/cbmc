SRC = bmc_util.cpp \
      solver_factory.cpp \
      symex_coverage.cpp \
      symex_bmc.cpp \
      # Empty last line

INCLUDES= -I ..

include ../config.inc
include ../common

CLEANFILES = goto-checker$(LIBEXT)

all: goto-checker$(LIBEXT)

###############################################################################

goto-checker$(LIBEXT): $(OBJ)
	$(LINKLIB)
