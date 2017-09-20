.PHONY: all cprover.dir test

# Source files for test utilities
SRC = src/expr/require_expr.cpp \
      src/ansi-c/c_to_expr.cpp \
      unit_tests.cpp \
      catch_example.cpp \
      util/expr_iterator.cpp \
      util/optional.cpp \
      analyses/call_graph.cpp \
      java_bytecode/java_bytecode_convert_class/convert_abstract_class.cpp \
      # Empty last line

# Test source files
SRC += unit_tests.cpp \
       analyses/ai/ai_simplify_lhs.cpp \
       analyses/call_graph.cpp \
       analyses/does_remove_const/does_expr_lose_const.cpp \
       analyses/does_remove_const/does_type_preserve_const_correctness.cpp \
       analyses/does_remove_const/is_type_at_least_as_const_as.cpp \
       java_bytecode/java_bytecode_convert_class/convert_abstract_class.cpp \
       java_bytecode/java_bytecode_parse_generics/parse_generic_class.cpp \
       miniBDD_new.cpp \
       solvers/refinement/string_constraint_generator_valueof/calculate_max_string_length.cpp \
       solvers/refinement/string_constraint_generator_valueof/get_numeric_value_from_character.cpp \
       solvers/refinement/string_constraint_generator_valueof/is_digit_with_radix.cpp \
       solvers/refinement/string_constraint_instantiation/instantiate_not_contains.cpp \
       solvers/refinement/string_refinement/concretize_array.cpp \
       solvers/refinement/string_refinement/substitute_array_list.cpp \
       util/expr_iterator.cpp \
       util/simplify_expr.cpp \
       catch_example.cpp \
       # Empty last line

INCLUDES= -I ../src/ -I.

include ../src/config.inc
include ../src/common

cprover.dir:
	$(MAKE) $(MAKEARGS) -C ../src

CPROVER_LIBS =../src/java_bytecode/java_bytecode$(LIBEXT) \
              ../src/miniz/miniz$(OBJEXT) \
              ../src/ansi-c/ansi-c$(LIBEXT) \
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
