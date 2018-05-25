.PHONY: all cprover.dir jprover.dir testing-utils.dir java-testing-utils.dir test

# Source files for test utilities
SRC = $(CPROVER_DIR)/unit/unit_tests.cpp \
      # Empty last line

# Test source files
SRC += java_bytecode/goto-programs/class_hierarchy_output.cpp \
       java_bytecode/goto-programs/class_hierarchy_graph.cpp \
       java_bytecode/goto-programs/remove_virtual_functions_without_fallback.cpp \
       java_bytecode/java_bytecode_convert_class/convert_abstract_class.cpp \
       java_bytecode/java_bytecode_convert_class/convert_java_annotations.cpp \
       java_bytecode/java_bytecode_convert_method/convert_invoke_dynamic.cpp \
       java_bytecode/java_bytecode_parse_generics/parse_generic_class.cpp \
       java_bytecode/java_object_factory/gen_nondet_string_init.cpp \
       java_bytecode/java_bytecode_parse_lambdas/java_bytecode_parse_lambda_method_table.cpp \
       java_bytecode/java_bytecode_parse_lambdas/java_bytecode_convert_class_lambda_method_handles.cpp \
       java_bytecode/java_string_library_preprocess/convert_exprt_to_string_exprt.cpp \
       java_bytecode/java_types/erase_type_arguments.cpp \
       java_bytecode/java_types/generic_type_index.cpp \
       java_bytecode/java_types/java_generic_symbol_type.cpp \
       java_bytecode/java_types/java_type_from_string.cpp \
       java_bytecode/java_utils_test.cpp \
       java_bytecode/inherited_static_fields/inherited_static_fields.cpp \
       pointer-analysis/custom_value_set_analysis.cpp \
       solvers/refinement/string_constraint_instantiation/instantiate_not_contains.cpp \
       solvers/refinement/string_refinement/dependency_graph.cpp \
       solvers/refinement/string_refinement/string_symbol_resolution.cpp \
       util/expr_iterator.cpp \
       util/has_subtype.cpp \
       util/parameter_indices.cpp \
       util/simplify_expr.cpp \
       java_bytecode/java_virtual_functions/virtual_functions.cpp \
       java_bytecode/java_bytecode_parse_generics/parse_generic_superclasses.cpp \
       # Empty last line

INCLUDES= -I ../src/ -I. -I $(CPROVER_DIR)/src -I $(CPROVER_DIR)/unit

include ../src/config.inc
include $(CPROVER_DIR)/src/config.inc
include $(CPROVER_DIR)/src/common

cprover.dir:
	$(MAKE) $(MAKEARGS) -C $(CPROVER_DIR)/src

jprover.dir:
	$(MAKE) $(MAKEARGS) -C ../src

cprover-testing-utils.dir:
	$(MAKE) $(MAKEARGS) -C $(CPROVER_DIR)/unit/testing-utils

java-testing-utils.dir:
	$(MAKE) $(MAKEARGS) -C java-testing-utils

# We need to link bmc.o to the unit test, so here's everything it depends on...
BMC_DEPS =$(CPROVER_DIR)/src/cbmc/all_properties$(OBJEXT) \
          $(CPROVER_DIR)/src/cbmc/bmc$(OBJEXT) \
          $(CPROVER_DIR)/src/cbmc/bmc_cover$(OBJEXT) \
          $(CPROVER_DIR)/src/cbmc/bv_cbmc$(OBJEXT) \
          $(CPROVER_DIR)/src/cbmc/cbmc_dimacs$(OBJEXT) \
          $(CPROVER_DIR)/src/cbmc/cbmc_languages$(OBJEXT) \
          $(CPROVER_DIR)/src/cbmc/cbmc_parse_options$(OBJEXT) \
          $(CPROVER_DIR)/src/cbmc/cbmc_solvers$(OBJEXT) \
          $(CPROVER_DIR)/src/cbmc/counterexample_beautification$(OBJEXT) \
          $(CPROVER_DIR)/src/cbmc/fault_localization$(OBJEXT) \
          $(CPROVER_DIR)/src/cbmc/show_vcc$(OBJEXT) \
          $(CPROVER_DIR)/src/cbmc/symex_bmc$(OBJEXT) \
          $(CPROVER_DIR)/src/cbmc/symex_coverage$(OBJEXT) \
          $(CPROVER_DIR)/src/cbmc/xml_interface$(OBJEXT) \
          $(CPROVER_DIR)/src/jsil/expr2jsil$(OBJEXT) \
          $(CPROVER_DIR)/src/jsil/jsil_convert$(OBJEXT) \
          $(CPROVER_DIR)/src/jsil/jsil_entry_point$(OBJEXT) \
          $(CPROVER_DIR)/src/jsil/jsil_internal_additions$(OBJEXT) \
          $(CPROVER_DIR)/src/jsil/jsil_language$(OBJEXT) \
          $(CPROVER_DIR)/src/jsil/jsil_lex.yy$(OBJEXT) \
          $(CPROVER_DIR)/src/jsil/jsil_parser$(OBJEXT) \
          $(CPROVER_DIR)/src/jsil/jsil_parse_tree$(OBJEXT) \
          $(CPROVER_DIR)/src/jsil/jsil_typecheck$(OBJEXT) \
          $(CPROVER_DIR)/src/jsil/jsil_types$(OBJEXT) \
          $(CPROVER_DIR)/src/jsil/jsil_y.tab$(OBJEXT) \
          # Empty last line

CPROVER_LIBS =../src/java_bytecode/java_bytecode$(LIBEXT) \
              ../src/miniz/miniz$(OBJEXT) \
              $(CPROVER_DIR)/src/ansi-c/ansi-c$(LIBEXT) \
              $(CPROVER_DIR)/src/cpp/cpp$(LIBEXT) \
              $(CPROVER_DIR)/src/json/json$(LIBEXT) \
              $(CPROVER_DIR)/src/linking/linking$(LIBEXT) \
              $(CPROVER_DIR)/src/util/util$(LIBEXT) \
              $(CPROVER_DIR)/src/big-int/big-int$(LIBEXT) \
              $(CPROVER_DIR)/src/goto-programs/goto-programs$(LIBEXT) \
              $(CPROVER_DIR)/src/goto-instrument/goto-instrument$(LIBEXT) \
              $(CPROVER_DIR)/src/pointer-analysis/pointer-analysis$(LIBEXT) \
              $(CPROVER_DIR)/src/langapi/langapi$(LIBEXT) \
              $(CPROVER_DIR)/src/assembler/assembler$(LIBEXT) \
              $(CPROVER_DIR)/src/analyses/analyses$(LIBEXT) \
              $(CPROVER_DIR)/src/solvers/solvers$(LIBEXT) \
              $(BMC_DEPS) \
              # Empty last line

OBJ += $(CPROVER_LIBS) \
       $(CPROVER_DIR)/unit/testing-utils/testing-utils$(LIBEXT) \
       java-testing-utils/java-testing-utils$(LIBEXT)

TESTS = unit_tests$(EXEEXT) \
        # Empty last line

CLEANFILES = $(TESTS)

all: cprover.dir cprover-testing-utils.dir jprover.dir java-testing-utils.dir
	$(MAKE) $(MAKEARGS) $(TESTS)

test: all
	$(foreach test,$(TESTS), (echo Running: $(test); ./$(test)) &&) true


###############################################################################

unit_tests$(EXEEXT): $(OBJ)
	$(LINKBIN)
