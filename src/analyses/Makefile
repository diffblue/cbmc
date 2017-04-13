SRC = natural_loops.cpp is_threaded.cpp dirty.cpp interval_analysis.cpp \
      invariant_set.cpp invariant_set_domain.cpp invariant_propagation.cpp \
      static_analysis.cpp uninitialized_domain.cpp local_may_alias.cpp \
      locals.cpp goto_check.cpp call_graph.cpp interval_domain.cpp \
      goto_rw.cpp reaching_definitions.cpp ai.cpp local_cfg.cpp \
      local_bitvector_analysis.cpp dependence_graph.cpp \
      constant_propagator.cpp replace_symbol_ext.cpp \
      flow_insensitive_analysis.cpp \
      custom_bitvector_analysis.cpp escape_analysis.cpp global_may_alias.cpp \
      does_remove_const.cpp \
      # Empty last line

INCLUDES= -I ..

include ../config.inc
include ../common

CLEANFILES = analyses$(LIBEXT)

all: analyses$(LIBEXT)

###############################################################################

analyses$(LIBEXT): $(OBJ)
	$(LINKLIB)
