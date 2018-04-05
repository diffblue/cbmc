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
       path_strategies.cpp \
       solvers/refinement/string_constraint_generator_valueof/calculate_max_string_length.cpp \
       solvers/refinement/string_constraint_generator_valueof/get_numeric_value_from_character.cpp \
       solvers/refinement/string_constraint_generator_valueof/is_digit_with_radix.cpp \
       solvers/refinement/string_refinement/concretize_array.cpp \
       solvers/refinement/string_refinement/substitute_array_list.cpp \
       solvers/refinement/string_refinement/sparse_array.cpp \
       solvers/refinement/string_refinement/union_find_replace.cpp \
       util/expr_cast/expr_cast.cpp \
       util/irep.cpp \
       util/irep_sharing.cpp \
       util/message.cpp \
       util/optional.cpp \
       util/sharing_node.cpp \
       util/sharing_map.cpp \
       util/small_map.cpp \
       util/small_shared_two_way_ptr.cpp \
       util/string_utils/split_string.cpp \
       util/string_utils/strip_string.cpp \
       util/symbol_table.cpp \
       catch_example.cpp \
       # Empty last line

INCLUDES= -I ../src/ -I.

include ../src/config.inc
include ../src/common

cprover.dir:
	$(MAKE) $(MAKEARGS) -C ../src

testing-utils.dir:
	$(MAKE) $(MAKEARGS) -C testing-utils

# We need to link bmc.o to the unit test, so here's everything it depends on...
BMC_DEPS =../src/cbmc/all_properties$(OBJEXT) \
          ../src/cbmc/bmc$(OBJEXT) \
          ../src/cbmc/bmc_cover$(OBJEXT) \
          ../src/cbmc/bv_cbmc$(OBJEXT) \
          ../src/cbmc/cbmc_dimacs$(OBJEXT) \
          ../src/cbmc/cbmc_languages$(OBJEXT) \
          ../src/cbmc/cbmc_parse_options$(OBJEXT) \
          ../src/cbmc/cbmc_solvers$(OBJEXT) \
          ../src/cbmc/counterexample_beautification$(OBJEXT) \
          ../src/cbmc/fault_localization$(OBJEXT) \
          ../src/cbmc/show_vcc$(OBJEXT) \
          ../src/cbmc/symex_bmc$(OBJEXT) \
          ../src/cbmc/symex_coverage$(OBJEXT) \
          ../src/cbmc/xml_interface$(OBJEXT) \
          ../src/jsil/expr2jsil$(OBJEXT) \
          ../src/jsil/jsil_convert$(OBJEXT) \
          ../src/jsil/jsil_entry_point$(OBJEXT) \
          ../src/jsil/jsil_internal_additions$(OBJEXT) \
          ../src/jsil/jsil_language$(OBJEXT) \
          ../src/jsil/jsil_lex.yy$(OBJEXT) \
          ../src/jsil/jsil_parser$(OBJEXT) \
          ../src/jsil/jsil_parse_tree$(OBJEXT) \
          ../src/jsil/jsil_typecheck$(OBJEXT) \
          ../src/jsil/jsil_types$(OBJEXT) \
          ../src/jsil/jsil_y.tab$(OBJEXT) \
          # Empty last line
#
CPROVER_LIBS =../src/ansi-c/ansi-c$(LIBEXT) \
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
              $(BMC_DEPS)
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
