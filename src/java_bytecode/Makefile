SRC = bytecode_info.cpp \
      character_refine_preprocess.cpp \
      ci_lazy_methods.cpp \
      ci_lazy_methods_needed.cpp \
      expr2java.cpp \
      generic_arguments_name_builder.cpp \
      jar_file.cpp \
      java_bytecode_convert_class.cpp \
      java_bytecode_convert_method.cpp \
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
      java_class_loader_limit.cpp \
      java_enum_static_init_unwind_handler.cpp \
      java_entry_point.cpp \
      java_local_variable_table.cpp \
      java_object_factory.cpp \
      java_pointer_casts.cpp \
      java_root_class.cpp \
      java_static_initializers.cpp \
      java_string_library_preprocess.cpp \
      java_string_literals.cpp \
      java_types.cpp \
      java_utils.cpp \
      generate_java_generic_type.cpp \
      mz_zip_archive.cpp \
      select_pointer_type.cpp \
      # Empty last line

INCLUDES= -I ..

include ../config.inc
include ../common

CLEANFILES = java_bytecode$(LIBEXT)

all: java_bytecode$(LIBEXT)

clean: clean_library

.PHONY: clean_library
clean_library:
	$(MAKE) clean -C library

library/java_core_models.inc:
	$(MAKE) -C library java_core_models.inc

java_class_loader$(OBJEXT): library/java_core_models.inc
###############################################################################

java_bytecode$(LIBEXT): $(OBJ)
	$(LINKLIB)
