.PHONY: all cprover.dir testing-utils.dir test

# Source files for test utilities
SRC = unit_tests.cpp \
      catch_example.cpp \
      # Empty last line

# Test source files
SRC += unit_tests.cpp \
       analyses/ai/ai_simplify_lhs.cpp \
       analyses/call_graph.cpp \
       analyses/does_remove_const/does_expr_lose_const.cpp \
       analyses/does_remove_const/does_type_preserve_const_correctness.cpp \
       analyses/does_remove_const/is_type_at_least_as_const_as.cpp \
       goto-programs/goto_trace_output.cpp \
       goto-programs/class_hierarchy_output.cpp \
       goto-programs/class_hierarchy_graph.cpp \
       goto-programs/remove_virtual_functions_without_fallback.cpp \
       java_bytecode/java_bytecode_convert_class/convert_abstract_class.cpp \
       java_bytecode/java_bytecode_convert_method/convert_invoke_dynamic.cpp \
       java_bytecode/java_bytecode_parse_generics/parse_generic_class.cpp \
       java_bytecode/java_object_factory/gen_nondet_string_init.cpp \
       java_bytecode/java_bytecode_parse_lambdas/java_bytecode_parse_lambda_method_table.cpp \
       java_bytecode/java_bytecode_parse_lambdas/java_bytecode_convert_class_lambda_method_handles.cpp \
       miniBDD_new.cpp \
       java_bytecode/java_string_library_preprocess/convert_exprt_to_string_exprt.cpp \
       java_bytecode/java_types/erase_type_arguments.cpp \
       java_bytecode/java_types/generic_type_index.cpp \
       java_bytecode/java_types/java_generic_symbol_type.cpp \
       java_bytecode/java_types/java_type_from_string.cpp \
       java_bytecode/java_utils_test.cpp \
       java_bytecode/inherited_static_fields/inherited_static_fields.cpp \
       pointer-analysis/custom_value_set_analysis.cpp \
       sharing_node.cpp \
       solvers/refinement/string_constraint_generator_valueof/calculate_max_string_length.cpp \
       solvers/refinement/string_constraint_generator_valueof/get_numeric_value_from_character.cpp \
       solvers/refinement/string_constraint_generator_valueof/is_digit_with_radix.cpp \
       solvers/refinement/string_constraint_instantiation/instantiate_not_contains.cpp \
       solvers/refinement/string_refinement/concretize_array.cpp \
       solvers/refinement/string_refinement/dependency_graph.cpp \
       solvers/refinement/string_refinement/substitute_array_list.cpp \
       solvers/refinement/string_refinement/string_symbol_resolution.cpp \
       solvers/refinement/string_refinement/sparse_array.cpp \
       solvers/refinement/string_refinement/union_find_replace.cpp \
       util/expr_cast/expr_cast.cpp \
       util/expr_iterator.cpp \
       util/has_subtype.cpp \
       util/irep.cpp \
       util/irep_sharing.cpp \
       util/message.cpp \
       util/optional.cpp \
       util/parameter_indices.cpp \
       util/simplify_expr.cpp \
       util/small_map.cpp \
       util/small_shared_two_way_ptr.cpp \
       util/string_utils/split_string.cpp \
       util/string_utils/strip_string.cpp \
       util/symbol_table.cpp \
       catch_example.cpp \
       java_bytecode/java_virtual_functions/virtual_functions.cpp \
       java_bytecode/java_bytecode_parse_generics/parse_generic_superclasses.cpp \
       # Empty last line

INCLUDES= -I ../src/ -I.

include ../src/config.inc
include ../src/common

cprover.dir:
	$(MAKE) $(MAKEARGS) -C ../src

testing-utils.dir:
	$(MAKE) $(MAKEARGS) -C testing-utils

CPROVER_LIBS =../src/java_bytecode/java_bytecode$(LIBEXT) \
              ../src/miniz/miniz$(OBJEXT) \
              ../src/ansi-c/ansi-c$(LIBEXT) \
              ../src/cpp/cpp$(LIBEXT) \
              ../src/json/json$(LIBEXT) \
              ../src/linking/linking$(LIBEXT) \
              ../src/util/util$(LIBEXT) \
              ../src/big-int/big-int$(LIBEXT) \
              ../src/goto-programs/goto-programs$(LIBEXT) \
              ../src/goto-instrument/goto-instrument$(LIBEXT) \
              ../src/pointer-analysis/pointer-analysis$(LIBEXT) \
              ../src/langapi/langapi$(LIBEXT) \
              ../src/assembler/assembler$(LIBEXT) \
              ../src/analyses/analyses$(LIBEXT) \
              ../src/solvers/solvers$(LIBEXT) \
              # Empty last line

OBJ += $(CPROVER_LIBS) testing-utils/testing-utils$(LIBEXT)

TESTS = unit_tests$(EXEEXT) \
        miniBDD$(EXEEXT) \
        # Empty last line

CLEANFILES = $(TESTS)

all: cprover.dir testing-utils.dir
	$(MAKE) $(MAKEARGS) $(TESTS)

test: all
	$(foreach test,$(TESTS), (echo Running: $(test); ./$(test)) &&) true


###############################################################################

unit_tests$(EXEEXT): $(OBJ)
	$(LINKBIN)

miniBDD$(EXEEXT): miniBDD$(OBJEXT) $(CPROVER_LIBS)
	$(LINKBIN)
