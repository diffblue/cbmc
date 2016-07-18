SRC = natural_loops.cpp is_threaded.cpp dirty.cpp interval_analysis.cpp \
      invariant_set.cpp invariant_set_domain.cpp invariant_propagation.cpp \
      uninitialized_domain.cpp local_may_alias.cpp \
      locals.cpp goto_check.cpp call_graph.cpp interval_domain.cpp \
      which_threads_internal.cpp lock_set_analysis.cpp lock_graph_analysis.cpp \
      local_bitvector_analysis.cpp dependence_graph.cpp \
      goto_rw.cpp reaching_definitions.cpp ai.cpp local_cfg.cpp \
      local_bitvector_analysis.cpp dependence_graph.cpp \
      constant_propagator.cpp replace_symbol_ext.cpp \
      flow_insensitive_analysis.cpp show_analysis.cpp \
      custom_bitvector_analysis.cpp escape_analysis.cpp global_may_alias.cpp \
      ai_cs.cpp ai_cs_stack.cpp lock_set_analysis_cs.cpp \
      lock_graph_cs.cpp lock_graph_analysis_cs.cpp non_concurrent.cpp \
      in_loop.cpp \
      get_target.cpp \
      simple_dependency_analysis.cpp \
      global_dependency_analysis.cpp

INCLUDES= -I ..

include ../config.inc
include ../common

CLEANFILES = analyses$(LIBEXT)

all: analyses$(LIBEXT)

###############################################################################

analyses$(LIBEXT): $(OBJ) 
	$(LINKLIB)

