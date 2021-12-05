SRC = ai.cpp \
      ai_domain.cpp \
      ai_history.cpp \
      call_graph.cpp \
      call_graph_helpers.cpp \
      call_stack_history.cpp \
      constant_propagator.cpp \
      custom_bitvector_analysis.cpp \
      dependence_graph.cpp \
      dirty.cpp \
      does_remove_const.cpp \
      escape_analysis.cpp \
      flow_insensitive_analysis.cpp \
      global_may_alias.cpp \
      goto_check.cpp \
      goto_check_c.cpp \
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
      local_control_flow_history.cpp \
      local_may_alias.cpp \
      local_safe_pointers.cpp \
      locals.cpp \
      reaching_definitions.cpp \
      sese_regions.cpp \
      static_analysis.cpp \
      uncaught_exceptions_analysis.cpp \
      uninitialized_domain.cpp \
      variable-sensitivity/abstract_environment.cpp \
      variable-sensitivity/abstract_object.cpp \
      variable-sensitivity/abstract_object_set.cpp \
      variable-sensitivity/abstract_pointer_object.cpp \
      variable-sensitivity/abstract_value_object.cpp \
      variable-sensitivity/constant_abstract_value.cpp \
      variable-sensitivity/constant_pointer_abstract_object.cpp \
      variable-sensitivity/context_abstract_object.cpp \
      variable-sensitivity/data_dependency_context.cpp \
      variable-sensitivity/full_array_abstract_object.cpp \
      variable-sensitivity/full_struct_abstract_object.cpp \
      variable-sensitivity/interval_abstract_value.cpp \
      variable-sensitivity/liveness_context.cpp \
      variable-sensitivity/three_way_merge_abstract_interpreter.cpp \
      variable-sensitivity/two_value_pointer_abstract_object.cpp \
      variable-sensitivity/value_set_abstract_object.cpp \
      variable-sensitivity/value_set_pointer_abstract_object.cpp \
      variable-sensitivity/variable_sensitivity_configuration.cpp \
      variable-sensitivity/variable_sensitivity_dependence_graph.cpp \
      variable-sensitivity/variable_sensitivity_domain.cpp \
      variable-sensitivity/variable_sensitivity_object_factory.cpp \
      variable-sensitivity/widened_range.cpp \
      variable-sensitivity/write_location_context.cpp \
      variable-sensitivity/write_stack.cpp \
      variable-sensitivity/write_stack_entry.cpp \
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
