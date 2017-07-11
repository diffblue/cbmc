SRC = ai.cpp \
      call_graph.cpp \
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
      interval_analysis.cpp \
      interval_domain.cpp \
      invariant_propagation.cpp \
      invariant_set.cpp \
      invariant_set_domain.cpp \
      is_threaded.cpp \
      local_bitvector_analysis.cpp \
      local_cfg.cpp \
      local_may_alias.cpp \
      locals.cpp \
      natural_loops.cpp \
      reaching_definitions.cpp \
      static_analysis.cpp \
      uninitialized_domain.cpp \
      variable-sensitivity/abstract_object.cpp \
      variable-sensitivity/abstract_enviroment.cpp \
      variable-sensitivity/abstract_value.cpp \
      variable-sensitivity/array_abstract_object.cpp \
      variable-sensitivity/constant_abstract_value.cpp \
      variable-sensitivity/constant_pointer_abstract_object.cpp \
      variable-sensitivity/pointer_abstract_object.cpp \
      variable-sensitivity/struct_abstract_object.cpp \
      variable-sensitivity/variable_sensitivity_domain.cpp \
      variable-sensitivity/variable_sensitivity_object_factory.cpp \
      variable-sensitivity/full_struct_abstract_object.cpp \
      variable-sensitivity/constant_array_abstract_object.cpp \
      variable-sensitivity/write_stack.cpp \
      variable-sensitivity/write_stack_entry.cpp \
      # Empty last line

INCLUDES= -I ..

include ../config.inc
include ../common

CLEANFILES = analyses$(LIBEXT)

all: analyses$(LIBEXT)

###############################################################################

analyses$(LIBEXT): $(OBJ)
	$(LINKLIB)
