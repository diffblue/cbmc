SRC = bytecode_info.cpp \
      character_refine_preprocess.cpp \
      ci_lazy_methods.cpp \
      ci_lazy_methods_needed.cpp \
      convert_java_nondet.cpp \
      expr2java.cpp \
      generic_parameter_specialization_map_keys.cpp \
      jar_file.cpp \
      jar_pool.cpp \
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
      java_object_factory.cpp \
      java_object_factory_parameters.cpp \
      java_pointer_casts.cpp \
      java_qualifiers.cpp \
      java_root_class.cpp \
      java_static_initializers.cpp \
      java_string_library_preprocess.cpp \
      java_string_literals.cpp \
      java_types.cpp \
      java_utils.cpp \
      load_method_by_regex.cpp \
      mz_zip_archive.cpp \
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

.PHONY: clean_library
clean_library:
	$(MAKE) clean -C library

.PHONY: library
library:
	$(MAKE) -C library

###############################################################################

java_bytecode$(LIBEXT): $(OBJ)
	$(LINKLIB)
