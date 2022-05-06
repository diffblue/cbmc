.PHONY: all cprover.dir test testing-utils-clean

# Source files for test utilities
SRC = unit_tests.cpp \
      # Empty last line

# Test source files
SRC += analyses/ai/ai.cpp \
       analyses/ai/ai_simplify_lhs.cpp \
       analyses/call_graph.cpp \
       analyses/constant_propagator.cpp \
       analyses/dependence_graph.cpp \
       analyses/disconnect_unreachable_nodes_in_graph.cpp \
       analyses/does_remove_const/does_expr_lose_const.cpp \
       analyses/does_remove_const/does_type_preserve_const_correctness.cpp \
       analyses/does_remove_const/is_type_at_least_as_const_as.cpp \
       analyses/variable-sensitivity/abstract_environment/to_predicate.cpp \
       analyses/variable-sensitivity/abstract_object/merge.cpp \
       analyses/variable-sensitivity/abstract_object/index_range.cpp \
       analyses/variable-sensitivity/constant_abstract_value/meet.cpp \
       analyses/variable-sensitivity/constant_abstract_value/merge.cpp \
       analyses/variable-sensitivity/constant_abstract_value/to_predicate.cpp \
       analyses/variable-sensitivity/constant_pointer_abstract_object/to_predicate.cpp \
       analyses/variable-sensitivity/full_array_abstract_object/array_builder.cpp \
       analyses/variable-sensitivity/full_array_abstract_object/maximum_length.cpp \
       analyses/variable-sensitivity/full_array_abstract_object/merge.cpp \
       analyses/variable-sensitivity/full_array_abstract_object/to_predicate.cpp \
       analyses/variable-sensitivity/eval.cpp \
       analyses/variable-sensitivity/eval-member-access.cpp \
       analyses/variable-sensitivity/interval_abstract_value/extremes-go-top.cpp \
       analyses/variable-sensitivity/interval_abstract_value/meet.cpp \
       analyses/variable-sensitivity/interval_abstract_value/merge.cpp \
       analyses/variable-sensitivity/interval_abstract_value/to_predicate.cpp \
       analyses/variable-sensitivity/interval_abstract_value/widening_merge.cpp \
       analyses/variable-sensitivity/full_struct_abstract_object/merge.cpp \
       analyses/variable-sensitivity/full_struct_abstract_object/struct_builder.cpp \
       analyses/variable-sensitivity/full_struct_abstract_object/to_predicate.cpp \
       analyses/variable-sensitivity/last_written_location.cpp \
       analyses/variable-sensitivity/value_expression_evaluation/assume.cpp \
       analyses/variable-sensitivity/value_expression_evaluation/assume_prune.cpp \
       analyses/variable-sensitivity/value_expression_evaluation/expression_evaluation.cpp \
       analyses/variable-sensitivity/value_set_abstract_object/extremes-go-top.cpp \
       analyses/variable-sensitivity/value_set_abstract_object/compacting.cpp \
       analyses/variable-sensitivity/value_set_abstract_object/meet.cpp \
       analyses/variable-sensitivity/value_set_abstract_object/merge.cpp \
       analyses/variable-sensitivity/value_set_abstract_object/to_predicate.cpp \
       analyses/variable-sensitivity/value_set_abstract_object/widening_merge.cpp \
       analyses/variable-sensitivity/value_set_pointer_abstract_object/to_predicate.cpp \
       analyses/variable-sensitivity/variable_sensitivity_domain/to_predicate.cpp \
       analyses/variable-sensitivity/variable_sensitivity_test_helpers.cpp \
       ansi-c/expr2c.cpp \
       ansi-c/max_malloc_size.cpp \
       ansi-c/type2name.cpp \
       big-int/big-int.cpp \
       compound_block_locations.cpp \
       get_goto_model_from_c_test.cpp \
       goto-cc/armcc_cmdline.cpp \
       goto-checker/properties/property_status.cpp \
       goto-checker/report_util/is_property_less_than.cpp \
       goto-instrument/cover_instrument.cpp \
       goto-instrument/cover/cover_only.cpp \
       goto-programs/allocate_objects.cpp \
       goto-programs/goto_program_assume.cpp \
       goto-programs/goto_program_dead.cpp \
       goto-programs/goto_program_declaration.cpp \
       goto-programs/goto_program_function_call.cpp \
       goto-programs/goto_program_goto_target.cpp \
       goto-programs/goto_program_symbol_type_table_consistency.cpp \
       goto-programs/goto_program_table_consistency.cpp \
       goto-programs/goto_program_validate.cpp \
       goto-programs/goto_trace_output.cpp \
       goto-programs/is_goto_binary.cpp \
       goto-programs/label_function_pointer_call_sites.cpp \
       goto-programs/osx_fat_reader.cpp \
       goto-programs/restrict_function_pointers.cpp \
       goto-programs/structured_trace_util.cpp \
       goto-programs/remove_returns.cpp \
       goto-programs/xml_expr.cpp \
       goto-symex/apply_condition.cpp \
       goto-symex/complexity_limiter.cpp \
       goto-symex/expr_skeleton.cpp \
       goto-symex/goto_symex_state.cpp \
       goto-symex/ssa_equation.cpp \
       goto-symex/is_constant.cpp \
       goto-symex/symex_assign.cpp \
       goto-symex/symex_level0.cpp \
       goto-symex/symex_level1.cpp \
       goto-symex/try_evaluate_pointer_comparisons.cpp \
       interpreter/interpreter.cpp \
       json/json_parser.cpp \
       json_symbol_table.cpp \
       path_strategies.cpp \
       pointer-analysis/value_set.cpp \
       solvers/bdd/miniBDD/miniBDD.cpp \
       solvers/floatbv/float_utils.cpp \
       solvers/lowering/byte_operators.cpp \
       solvers/prop/bdd_expr.cpp \
       solvers/sat/external_sat.cpp \
       solvers/sat/satcheck_cadical.cpp \
       solvers/sat/satcheck_minisat2.cpp \
       solvers/smt2/smt2_conv.cpp \
       solvers/smt2/smt2irep.cpp \
       solvers/smt2_incremental/construct_value_expr_from_smt.cpp \
       solvers/smt2_incremental/convert_expr_to_smt.cpp \
       solvers/smt2_incremental/object_tracking.cpp \
       solvers/smt2_incremental/smt2_incremental_decision_procedure.cpp \
       solvers/smt2_incremental/smt_bit_vector_theory.cpp \
       solvers/smt2_incremental/smt_commands.cpp \
       solvers/smt2_incremental/smt_core_theory.cpp \
       solvers/smt2_incremental/smt_index.cpp \
       solvers/smt2_incremental/smt_object_size.cpp \
       solvers/smt2_incremental/smt_response_validation.cpp \
       solvers/smt2_incremental/smt_responses.cpp \
       solvers/smt2_incremental/smt_sorts.cpp \
       solvers/smt2_incremental/smt_terms.cpp \
       solvers/smt2_incremental/smt_to_smt2_string.cpp \
       solvers/strings/array_pool/array_pool.cpp \
       solvers/strings/string_constraint_generator_valueof/calculate_max_string_length.cpp \
       solvers/strings/string_constraint_generator_valueof/get_numeric_value_from_character.cpp \
       solvers/strings/string_constraint_generator_valueof/is_digit_with_radix.cpp \
       solvers/strings/string_format_builtin_function/length_for_format_specifier.cpp \
       solvers/strings/string_format_builtin_function/length_of_decimal_int.cpp \
       solvers/strings/string_refinement/concretize_array.cpp \
       solvers/strings/string_refinement/sparse_array.cpp \
       solvers/strings/string_refinement/string_refinement.cpp \
       solvers/strings/string_refinement/substitute_array_list.cpp \
       solvers/strings/string_refinement/union_find_replace.cpp \
       util/bitvector_expr.cpp \
       util/cmdline.cpp \
       util/dense_integer_map.cpp \
       util/edit_distance.cpp \
       util/expr_cast/expr_cast.cpp \
       util/expr.cpp \
       util/expr_iterator.cpp \
       util/file_util.cpp \
       util/format.cpp \
       util/format_number_range.cpp \
       util/get_base_name.cpp \
       util/graph.cpp \
       util/interval/add.cpp \
       util/interval/bitwise.cpp \
       util/interval/comparisons.cpp \
       util/interval/divide.cpp \
       util/interval/eval.cpp \
       util/interval/get_extreme.cpp \
       util/interval/modulo.cpp \
       util/interval/multiply.cpp \
       util/interval/shift.cpp \
       util/interval/subtract.cpp \
       util/interval/to_string.cpp \
       util/interval_constraint.cpp \
       util/interval_union.cpp \
       util/irep.cpp \
       util/irep_sharing.cpp \
       util/invariant.cpp \
       util/json_array.cpp \
       util/json_object.cpp \
       util/lazy.cpp \
       util/memory_info.cpp \
       util/message.cpp \
       util/optional.cpp \
       util/optional_utils.cpp \
       util/parse_options.cpp \
       util/piped_process.cpp \
       util/pointer_expr.cpp \
       util/pointer_offset_size.cpp \
       util/prefix_filter.cpp \
       util/range.cpp \
       util/replace_symbol.cpp \
       util/run.cpp \
       util/sharing_map.cpp \
       util/sharing_node.cpp \
       util/simplify_expr.cpp \
       util/small_map.cpp \
       util/small_shared_n_way_ptr.cpp \
       util/ssa_expr.cpp \
       util/std_expr.cpp \
       util/string2int.cpp \
       util/structured_data.cpp \
       util/string_utils/capitalize.cpp \
       util/string_utils/escape_non_alnum.cpp \
       util/string_utils/join_string.cpp \
       util/string_utils/split_string.cpp \
       util/string_utils/strip_string.cpp \
       util/string_utils/wrap_line.cpp \
       util/symbol_table.cpp \
       util/symbol.cpp \
       util/unicode.cpp \
       util/xml.cpp \
       # Empty last line

ifeq ($(OS),Windows_NT)
    detected_OS := Windows
else
    detected_OS := $(shell sh -c 'uname 2>/dev/null || echo Unknown')
endif

ifeq ($(detected_OS),Linux)
  ifneq ($(WITH_MEMORY_ANALYZER),0)
    # only set if it wasn't explicitly unset
    WITH_MEMORY_ANALYZER=1
  endif
endif

ifeq ($(WITH_MEMORY_ANALYZER),1)
  SRC += memory-analyzer/gdb_api.cpp
endif

INCLUDES= -I ../src/ -I.

CPROVER_DIR = .
include ../src/config.inc
include ../src/common

cprover.dir:
	$(MAKE) $(MAKEARGS) -C ../src

testing-utils/testing-utils$(LIBEXT): cprover.dir
	$(MAKE) $(MAKEARGS) -C testing-utils

testing-utils-clean:
	$(MAKE) $(MAKEARGS) -C testing-utils clean

# We need to link bmc.o to the unit test, so here's everything it depends on...
BMC_DEPS =../src/cbmc/c_test_input_generator$(OBJEXT) \
          ../src/cbmc/cbmc_languages$(OBJEXT) \
          ../src/cbmc/cbmc_parse_options$(OBJEXT) \
          ../src/goto-cc/armcc_cmdline$(OBJEXT) \
          ../src/goto-cc/goto_cc_cmdline$(OBJEXT) \
          ../src/goto-instrument/source_lines$(OBJEXT) \
          ../src/goto-instrument/cover$(OBJEXT) \
          ../src/goto-instrument/cover_basic_blocks$(OBJEXT) \
          ../src/goto-instrument/cover_filter$(OBJEXT) \
          ../src/goto-instrument/cover_instrument_assume$(OBJEXT) \
          ../src/goto-instrument/cover_instrument_branch$(OBJEXT) \
          ../src/goto-instrument/cover_instrument_condition$(OBJEXT) \
          ../src/goto-instrument/cover_instrument_decision$(OBJEXT) \
          ../src/goto-instrument/cover_instrument_location$(OBJEXT) \
          ../src/goto-instrument/cover_instrument_mcdc$(OBJEXT) \
          ../src/goto-instrument/cover_instrument_other$(OBJEXT) \
          ../src/goto-instrument/cover_util$(OBJEXT) \
          ../src/goto-instrument/goto_program2code$(OBJEXT) \
          ../src/goto-instrument/reachability_slicer$(OBJEXT) \
          ../src/goto-instrument/nondet_static$(OBJEXT) \
          ../src/goto-instrument/full_slicer$(OBJEXT) \
          ../src/goto-instrument/unwindset$(OBJEXT) \
          ../src/xmllang/xmllang$(LIBEXT) \
          ../src/goto-symex/goto-symex$(LIBEXT) \
          ../src/jsil/jsil$(LIBEXT) \
          # Empty last line
#
CPROVER_LIBS =../src/ansi-c/ansi-c$(LIBEXT) \
              ../src/cpp/cpp$(LIBEXT) \
              ../src/json/json$(LIBEXT) \
              ../src/json-symtab-language/json-symtab-language$(LIBEXT) \
              ../src/linking/linking$(LIBEXT) \
              ../src/util/util$(LIBEXT) \
              ../src/big-int/big-int$(LIBEXT) \
              ../src/goto-checker/goto-checker$(LIBEXT) \
              ../src/goto-programs/goto-programs$(LIBEXT) \
              ../src/pointer-analysis/pointer-analysis$(LIBEXT) \
              ../src/langapi/langapi$(LIBEXT) \
              ../src/assembler/assembler$(LIBEXT) \
              ../src/analyses/analyses$(LIBEXT) \
              ../src/solvers/solvers$(LIBEXT) \
              ../src/statement-list/statement-list$(LIBEXT) \
              $(BMC_DEPS)
              # Empty last line

OBJ += $(CPROVER_LIBS) testing-utils/testing-utils$(LIBEXT)

CATCH_TEST = unit_tests$(EXEEXT)
EXCLUDED_TESTS=expr_undefined_casts.cpp
ifneq ($(WITH_MEMORY_ANALYZER),1)
EXCLUDED_TESTS += gdb_api.cpp
endif
ifeq ($(MINISAT2),)
EXCLUDED_TESTS += satcheck_minisat2.cpp
endif
ifeq ($(CADICAL),)
EXCLUDED_TESTS += satcheck_cadical.cpp
endif

N_CATCH_TESTS = $(shell ./count_tests.py --exclude-files "$(EXCLUDED_TESTS)")

memory-analyzer/input.inc: memory-analyzer/input.txt
	../src/ansi-c/file_converter$(EXEEXT) $< > $@

memory-analyzer/test.inc: memory-analyzer/test.c
	../src/ansi-c/file_converter$(EXEEXT) $< > $@

memory-analyzer/gdb_api$(OBJEXT): memory-analyzer/input.inc memory-analyzer/test.inc

CLEANFILES = $(CATCH_TEST) testing-utils/testing-utils$(LIBEXT) \
             memory-analyzer/input.inc memory-analyzer/test.inc

# only add a dependency for libraries to avoid triggering implicit rules, which
# would cause unnecessary rebuilds
$(filter %$(LIBEXT), $(CPROVER_LIBS)): cprover.dir

all: $(CATCH_TEST)

clean: testing-utils-clean

test: $(CATCH_TEST)
	# Include hidden tests by specifying "*,[.]" for tests to count
	if ! ./$(CATCH_TEST) "*,[.]" -l | grep -q "^$(N_CATCH_TESTS) matching test cases" ; then \
		./$(CATCH_TEST) "*,[.]" -l ; fi
	./$(CATCH_TEST) ${TAGS}


###############################################################################

unit_tests$(EXEEXT): $(OBJ)
	$(LINKBIN)
