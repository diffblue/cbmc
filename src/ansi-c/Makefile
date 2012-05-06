SRC = c_typecast.cpp y.tab.cpp lex.yy.cpp ansi_c_parser.cpp \
      expr2c.cpp ansi_c_language.cpp c_sizeof.cpp c_main.cpp \
      c_types.cpp trans_unit.cpp ansi_c_typecheck.cpp \
      c_link.cpp c_preprocess.cpp c_link_type_eq.cpp \
      c_typecheck_base.cpp c_typecheck_initializer.cpp \
      c_typecheck_typecast.cpp c_typecheck_code.cpp \
      c_typecheck_expr.cpp c_typecheck_type.cpp string_constant.cpp \
      c_qualifiers.cpp c_typecheck_argc_argv.cpp ansi_c_parse_tree.cpp \
      preprocessor_line.cpp ansi_c_convert.cpp ansi_c_convert_type.cpp \
      type2name.cpp cprover_library.cpp anonymous_member.cpp \
      printf_formatter.cpp internal_additions.cpp padding.cpp \
      ansi_c_declaration.cpp designator.cpp concatenate_strings.cpp \
      literals/parse_float.cpp literals/unescape_string.cpp \
      literals/convert_float_literal.cpp \
      literals/convert_character_literal.cpp \
      literals/convert_integer_literal.cpp \
      literals/convert_string_literal.cpp \
      remove_internal_symbols.cpp

INCLUDES= -I .. -I ../util

include ../config.inc
include ../common

CLEANFILES = ansi-c$(LIBEXT) \
  y.tab.h y.tab.cpp lex.yy.cpp y.tab.cpp.output y.output \
  library/converter$(EXEEXT) cprover_library.inc

all: ansi-c$(LIBEXT)

###############################################################################

y.tab.cpp: parser.y
	$(YACC) $(YFLAGS) $$flags -pyyansi_c -d parser.y -o y.tab.cpp

y.tab.h: y.tab.cpp
	if [ -e y.tab.hpp ] ; then mv y.tab.hpp y.tab.h ; else \
        mv y.tab.cpp.h y.tab.h ; fi

lex.yy.cpp: scanner.l
	$(LEX) -Pyyansi_c -o$@ scanner.l

# extra dependencies
y.tab$(OBJEXT): y.tab.cpp y.tab.h
lex.yy$(OBJEXT): y.tab.cpp lex.yy.cpp y.tab.h
cprover_library$(OBJEXT): cprover_library.inc

###############################################################################

library/converter$(EXEEXT): library/converter.cpp
	$(LINKBIN)
	
cprover_library.inc: library/converter$(EXEEXT) library/*.c
	cat library/*.c | library/converter > $@

cprover_library.cpp: cprover_library.inc

###############################################################################

ansi-c$(LIBEXT): $(OBJ) 
	$(LINKLIB)

