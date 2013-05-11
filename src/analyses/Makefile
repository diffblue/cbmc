SRC = natural_loops.cpp is_threaded.cpp dirty.cpp interval_analysis.cpp \
      invariant_set.cpp invariant_set_domain.cpp invariant_propagation.cpp \
      static_analysis.cpp uninitialized_domain.cpp local_may_alias.cpp \
      locals.cpp goto_check.cpp call_graph.cpp 

INCLUDES= -I ..

include ../config.inc
include ../common

CLEANFILES = analyses$(LIBEXT)

all: analyses$(LIBEXT)

###############################################################################

analyses$(LIBEXT): $(OBJ) 
	$(LINKLIB)

