SRC = cfg_dominators.cpp natural_loops.cpp is_threaded.cpp dirty.cpp \
      invariant_set.cpp invariant_set_domain.cpp invariant_propagation.cpp \
      static_analysis.cpp uninitialized_domain.cpp local_may_alias.cpp \
      locals.cpp

INCLUDES= -I .. -I ../util

include ../config.inc
include ../common

CLEANFILES = analyses$(LIBEXT)

all: analyses$(LIBEXT)

###############################################################################

analyses$(LIBEXT): $(OBJ) 
	$(LINKLIB)

