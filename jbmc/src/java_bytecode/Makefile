SRC = assignments_from_json.cpp \
      bytecode_info.cpp \
      character_refine_preprocess.cpp \
      ci_lazy_methods.cpp \
      ci_lazy_methods_needed.cpp \
      code_with_references.cpp \
      convert_java_nondet.cpp \
      create_array_with_type_intrinsic.cpp \
      expr2java.cpp \
      generic_parameter_specialization_map.cpp \
      generic_parameter_specialization_map_keys.cpp \
      jar_file.cpp \
      jar_pool.cpp \
      java_bmc_util.cpp \
      java_bytecode_convert_class.cpp \
      java_bytecode_convert_method.cpp \
      java_bytecode_concurrency_instrumentation.cpp \
      java_bytecode_instrument.cpp \
      java_bytecode_internal_additions.cpp \
      java_bytecode_language.cpp \
      java_bytecode_parse_tree.cpp \
      java_bytecode_parser.cpp \
      java_bytecode_typecheck.cpp \
      java_bytecode_typecheck_code.cpp \
      java_bytecode_typecheck_expr.cpp \
      java_bytecode_typecheck_type.cpp \
      java_class_loader.cpp \
      java_class_loader_base.cpp \
      java_class_loader_limit.cpp \
      java_enum_static_init_unwind_handler.cpp \
      java_entry_point.cpp \
      java_local_variable_table.cpp \
      java_multi_path_symex_checker.cpp \
      java_object_factory.cpp \
      java_object_factory_parameters.cpp \
      java_pointer_casts.cpp \
      java_qualifiers.cpp \
      java_root_class.cpp \
      java_single_path_symex_checker.cpp \
      java_static_initializers.cpp \
      java_string_library_preprocess.cpp \
      java_string_literals.cpp \
      java_trace_validation.cpp \
      java_types.cpp \
      java_utils.cpp \
      lambda_synthesis.cpp \
      lazy_goto_model.cpp \
      lift_clinit_calls.cpp \
      load_method_by_regex.cpp \
      mz_zip_archive.cpp \
      nondet.cpp \
      remove_exceptions.cpp \
      remove_instanceof.cpp \
      remove_java_new.cpp \
      replace_java_nondet.cpp \
      select_pointer_type.cpp \
      simple_method_stubbing.cpp \
      # Empty last line

INCLUDES= -I .. -I ../$(CPROVER_DIR)/src

include ../config.inc
include ../$(CPROVER_DIR)/src/config.inc
include ../$(CPROVER_DIR)/src/common

CLEANFILES = java_bytecode$(LIBEXT)

all: library java_bytecode$(LIBEXT)

clean: clean_library

LIBRARY_DIR = ../../lib/java-models-library

.PHONY: clean_library
clean_library:
	if [ -d $(LIBRARY_DIR) ]; then cd $(LIBRARY_DIR); mvn --quiet clean; fi

.PHONY: library
library:
	if [ -d $(LIBRARY_DIR) ]; then \
		(cd $(LIBRARY_DIR); mvn --quiet -Dmaven.test.skip=true package); \
	fi

###############################################################################

java_bytecode$(LIBEXT): $(OBJ)
	$(LINKLIB)
