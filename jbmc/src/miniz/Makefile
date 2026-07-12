SRC = miniz.cpp \
      # Empty last line

INCLUDES= -I ../$(CPROVER_DIR)/src

include ../config.inc
include ../$(CPROVER_DIR)/src/config.inc
include ../$(CPROVER_DIR)/src/common

# the miniz sources are in the third-party directory 3p/
vpath miniz.cpp ../$(CPROVER_DIR)/3p/miniz-3.0.2

CLEANFILES = miniz$(OBJEXT)

all: miniz$(OBJEXT)

###############################################################################
