SRC = cpp_id.cpp cpp_language.cpp expr2cpp.cpp cpp_parser.cpp \
      lex.yy.cpp cpp_typecheck.cpp cpp_convert_type.cpp \
      cpp_typecheck_expr.cpp cpp_typecheck_code.cpp \
      cpp_typecheck_type.cpp parse.cpp cpp_parse_tree.cpp \
      cpp_token_buffer.cpp cpp_typecheck_fargs.cpp \
      cpp_typecheck_resolve.cpp cpp_util.cpp cpp_enum_type.cpp \
      cpp_typecheck_function.cpp cpp_typecheck_namespace.cpp \
      cpp_name.cpp cpp_is_pod.cpp cpp_scope.cpp \
      cpp_typecheck_find_constructor.cpp template_map.cpp \
      cpp_scopes.cpp cpp_declarator.cpp cpp_instantiate_template.cpp \
      internal_additions.cpp cpp_type2name.cpp \
      cpp_typecheck_linkage_spec.cpp \
      cpp_typecheck_template.cpp cpp_typecheck_function_bodies.cpp \
      cpp_typecheck_initializer.cpp cpp_typecheck_compound_type.cpp \
      cpp_constructor.cpp cpp_destructor.cpp \
      cpp_final.cpp cpp_typecheck_conversions.cpp\
      cpp_typecheck_declaration.cpp cpp_declarator_converter.cpp \
      cpp_declaration.cpp cpp_namespace_spec.cpp \
      cpp_typecheck_using.cpp cpp_exception_id.cpp \
      cpp_typecheck_enum_type.cpp cpp_typecheck_bases.cpp \
      cpp_typecheck_constructor.cpp cpp_typecheck_virtual_table.cpp

INCLUDES= -I .. -I ../util

include ../config.inc
include ../common

CLEANFILES = cpp$(LIBEXT) lex.yy.cpp y.tab.cpp.output

all: cpp$(LIBEXT)

###############################################################################

cpp$(LIBEXT): $(OBJ)
	$(LINKLIB)

lex.yy.cpp: scanner.l
	$(LEX) -Pyycpp -olex.yy.cpp scanner.l

lex.yy$(OBJEXT): lex.yy.cpp

