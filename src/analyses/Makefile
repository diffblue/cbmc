SRC = ai.cpp \
      ai_domain.cpp \
      ai_history.cpp \
      call_graph.cpp \
      call_graph_helpers.cpp \
      constant_propagator.cpp \
      custom_bitvector_analysis.cpp \
      dependence_graph.cpp \
      dirty.cpp \
      does_remove_const.cpp \
      escape_analysis.cpp \
      flow_insensitive_analysis.cpp \
      global_may_alias.cpp \
      goto_check.cpp \
      goto_rw.cpp \
      guard_bdd.cpp \
      guard_expr.cpp \
      interval_analysis.cpp \
      interval_domain.cpp \
      invariant_propagation.cpp \
      invariant_set.cpp \
      invariant_set_domain.cpp \
      is_threaded.cpp \
      local_bitvector_analysis.cpp \
      local_cfg.cpp \
      local_may_alias.cpp \
      local_safe_pointers.cpp \
      locals.cpp \
      reaching_definitions.cpp \
      sese_regions.cpp \
      static_analysis.cpp \
      uncaught_exceptions_analysis.cpp \
      uninitialized_domain.cpp \
      # Empty last line

INCLUDES= -I ..

include ../config.inc
include ../common

CLEANFILES = analyses$(LIBEXT)

all: analyses$(LIBEXT)

ifneq ($(CUDD),)
  OBJ += $(CUDD)/cudd/.libs/libcudd$(LIBEXT) $(CUDD)/cplusplus/.libs/libobj$(LIBEXT)
endif

###############################################################################

analyses$(LIBEXT): $(OBJ)
	$(LINKLIB)
