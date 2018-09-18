SRC = cpp_constructor.cpp \
      cpp_convert_type.cpp \
      cpp_declaration.cpp \
      cpp_declarator.cpp \
      cpp_declarator_converter.cpp \
      cpp_destructor.cpp \
      cpp_enum_type.cpp \
      cpp_exception_id.cpp \
      cpp_id.cpp \
      cpp_instantiate_template.cpp \
      cpp_internal_additions.cpp \
      cpp_is_pod.cpp \
      cpp_language.cpp \
      cpp_name.cpp \
      cpp_namespace_spec.cpp \
      cpp_parse_tree.cpp \
      cpp_parser.cpp \
      cpp_scope.cpp \
      cpp_scopes.cpp \
      cpp_token_buffer.cpp \
      cpp_type2name.cpp \
      cpp_typecheck.cpp \
      cpp_typecheck_bases.cpp \
      cpp_typecheck_code.cpp \
      cpp_typecheck_compound_type.cpp \
      cpp_typecheck_constructor.cpp \
      cpp_typecheck_conversions.cpp \
      cpp_typecheck_declaration.cpp \
      cpp_typecheck_destructor.cpp \
      cpp_typecheck_enum_type.cpp \
      cpp_typecheck_expr.cpp \
      cpp_typecheck_fargs.cpp \
      cpp_typecheck_function.cpp \
      cpp_typecheck_initializer.cpp \
      cpp_typecheck_linkage_spec.cpp \
      cpp_typecheck_method_bodies.cpp \
      cpp_typecheck_namespace.cpp \
      cpp_typecheck_resolve.cpp \
      cpp_typecheck_static_assert.cpp \
      cpp_typecheck_template.cpp \
      cpp_typecheck_type.cpp \
      cpp_typecheck_using.cpp \
      cpp_typecheck_virtual_table.cpp \
      cpp_util.cpp \
      cprover_library.cpp \
      expr2cpp.cpp \
      parse.cpp \
      template_map.cpp \
      # Empty last line

INCLUDES= -I ..

include ../config.inc
include ../common

CLEANFILES = cpp$(LIBEXT) cprover_library.inc library_check

all: cpp$(LIBEXT)

###############################################################################

# extra dependencies
cprover_library$(OBJEXT): cprover_library.inc

###############################################################################

../ansi-c/library/converter$(EXEEXT): ../ansi-c/library/converter.cpp
	$(MAKE) -C ../ansi-c library/converter$(EXEEXT)

library_check: library/*.c
	../ansi-c/library_check.sh $(CC) $^
	touch $@

cprover_library.inc: ../ansi-c/library/converter$(EXEEXT) library/*.c
	cat library/*.c | ../ansi-c/library/converter$(EXEEXT) > $@

generated_files: cprover_library.inc

###############################################################################

cpp$(LIBEXT): $(OBJ)
	$(LINKLIB)
