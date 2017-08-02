.PHONY: all cprover.dir test

# Source files for test utilities
SRC = src/expr/require_expr.cpp \
      src/ansi-c/c_to_expr.cpp \
      unit_tests.cpp \
      catch_example.cpp \
      util/expr_iterator.cpp \
      analyses/call_graph.cpp \
      java_bytecode/java_bytecode_convert_class/convert_abstract_class.cpp \
      solvers/refinement/string_constraint_generator_valueof/is_digit_with_radix.cpp \
      solvers/refinement/string_constraint_generator_valueof/get_numeric_value_from_character.cpp \
      # Empty last line

# Test source files
SRC += unit_tests.cpp \
       analyses/ai/ai_simplify_lhs.cpp \
       analyses/does_remove_const/does_expr_lose_const.cpp \
       analyses/does_remove_const/does_type_preserve_const_correctness.cpp \
       analyses/does_remove_const/is_type_at_least_as_const_as.cpp \
       miniBDD_new.cpp \
       catch_example.cpp \
       analyses/call_graph.cpp \
       java_bytecode/java_bytecode_convert_class/convert_abstract_class.cpp \
       solvers/refinement/string_constraint_generator_valueof/is_digit_with_radix.cpp \
      solvers/refinement/string_constraint_generator_valueof/is_digit_with_radix_lower_case.cpp \
       solvers/refinement/string_constraint_generator_valueof/get_numeric_value_from_character.cpp \
       # Empty last line

INCLUDES= -I ../src/ -I.

include ../src/config.inc
include ../src/common

cprover.dir:
	$(MAKE) $(MAKEARGS) -C ../src

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
              # Empty last line

OBJ += $(CPROVER_LIBS)

TESTS = unit_tests$(EXEEXT) \
        miniBDD$(EXEEXT) \
        string_utils$(EXEEXT) \
        sharing_node$(EXEEXT) \
        # Empty last line

CLEANFILES = $(TESTS)

all: cprover.dir
	$(MAKE) $(MAKEARGS) $(TESTS)

test: all
	$(foreach test,$(TESTS), (echo Running: $(test); ./$(test)) &&) true


###############################################################################

unit_tests$(EXEEXT): $(OBJ)
	$(LINKBIN)

miniBDD$(EXEEXT): miniBDD$(OBJEXT) $(CPROVER_LIBS)
	$(LINKBIN)

string_utils$(EXEEXT): string_utils$(OBJEXT) $(CPROVER_LIBS)
	$(LINKBIN)

sharing_node$(EXEEXT): sharing_node$(OBJEXT) $(CPROVER_LIBS)
	$(LINKBIN)
