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
       goto-programs/goto_trace_output.cpp \
       interpreter/interpreter.cpp \
       json/json_parser.cpp \
       path_strategies.cpp \
       pointer-analysis/value_set.cpp \
       solvers/floatbv/float_utils.cpp \
       solvers/miniBDD/miniBDD.cpp \
       solvers/refinement/array_pool/array_pool.cpp \
       solvers/refinement/string_constraint_generator_valueof/calculate_max_string_length.cpp \
       solvers/refinement/string_constraint_generator_valueof/get_numeric_value_from_character.cpp \
       solvers/refinement/string_constraint_generator_valueof/is_digit_with_radix.cpp \
       solvers/refinement/string_refinement/concretize_array.cpp \
       solvers/refinement/string_refinement/sparse_array.cpp \
       solvers/refinement/string_refinement/substitute_array_list.cpp \
       solvers/refinement/string_refinement/union_find_replace.cpp \
       util/expr_cast/expr_cast.cpp \
       util/expr.cpp \
       util/file_util.cpp \
       util/get_base_name.cpp \
       util/graph.cpp \
       util/irep.cpp \
       util/irep_sharing.cpp \
       util/message.cpp \
       util/optional.cpp \
       util/replace_symbol.cpp \
       util/sharing_map.cpp \
       util/sharing_node.cpp \
       util/small_map.cpp \
       util/small_shared_two_way_ptr.cpp \
			 util/std_expr.cpp \
       util/string_utils/split_string.cpp \
       util/string_utils/strip_string.cpp \
       util/symbol_table.cpp \
       util/unicode.cpp \
       # Empty last line

INCLUDES= -I ../src/ -I.

include ../src/config.inc
include ../src/common

cprover.dir:
	$(MAKE) $(MAKEARGS) -C ../src

testing-utils/testing-utils$(LIBEXT): cprover.dir
	$(MAKE) $(MAKEARGS) -C testing-utils

testing-utils-clean:
	$(MAKE) $(MAKEARGS) -C testing-utils clean

# We need to link bmc.o to the unit test, so here's everything it depends on...
BMC_DEPS =../src/cbmc/all_properties$(OBJEXT) \
          ../src/cbmc/bmc$(OBJEXT) \
          ../src/cbmc/bmc_cover$(OBJEXT) \
          ../src/cbmc/cbmc_languages$(OBJEXT) \
          ../src/cbmc/cbmc_parse_options$(OBJEXT) \
          ../src/cbmc/cbmc_solvers$(OBJEXT) \
          ../src/cbmc/counterexample_beautification$(OBJEXT) \
          ../src/cbmc/fault_localization$(OBJEXT) \
          ../src/cbmc/symex_bmc$(OBJEXT) \
          ../src/cbmc/symex_coverage$(OBJEXT) \
          ../src/cbmc/xml_interface$(OBJEXT) \
          ../src/goto-instrument/cover$(OBJEXT) \
          ../src/goto-instrument/cover_basic_blocks$(OBJEXT) \
          ../src/goto-instrument/cover_filter$(OBJEXT) \
          ../src/goto-instrument/cover_instrument_branch$(OBJEXT) \
          ../src/goto-instrument/cover_instrument_condition$(OBJEXT) \
          ../src/goto-instrument/cover_instrument_decision$(OBJEXT) \
          ../src/goto-instrument/cover_instrument_location$(OBJEXT) \
          ../src/goto-instrument/cover_instrument_mcdc$(OBJEXT) \
          ../src/goto-instrument/cover_instrument_other$(OBJEXT) \
          ../src/goto-instrument/cover_util$(OBJEXT) \
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
              ../src/linking/linking$(LIBEXT) \
              ../src/util/util$(LIBEXT) \
              ../src/big-int/big-int$(LIBEXT) \
              ../src/goto-programs/goto-programs$(LIBEXT) \
              ../src/pointer-analysis/pointer-analysis$(LIBEXT) \
              ../src/langapi/langapi$(LIBEXT) \
              ../src/assembler/assembler$(LIBEXT) \
              ../src/analyses/analyses$(LIBEXT) \
              ../src/solvers/solvers$(LIBEXT) \
              $(BMC_DEPS)
              # Empty last line

OBJ += $(CPROVER_LIBS) testing-utils/testing-utils$(LIBEXT)

CATCH_TEST = unit_tests$(EXEEXT)
N_CATCH_TESTS = $(shell \
                  cat $$(find . -name "*.cpp" \
                    -a -not -name "expr_undefined_casts.cpp") | \
                  grep -c -E "(SCENARIO|TEST_CASE)")

CLEANFILES = $(CATCH_TEST) testing-utils/testing-utils$(LIBEXT)

# only add a dependency for libraries to avoid triggering implicit rules, which
# would cause unnecessary rebuilds
$(filter %$(LIBEXT), CPROVER_LIBS): cprover.dir

all: $(CATCH_TEST)

clean: testing-utils-clean

test: $(CATCH_TEST)
	if ! ./$(CATCH_TEST) -l | grep -q "^$(N_CATCH_TESTS) test cases" ; then \
		./$(CATCH_TEST) -l ; fi
	./$(CATCH_TEST)


###############################################################################

unit_tests$(EXEEXT): $(OBJ)
	$(LINKBIN)
