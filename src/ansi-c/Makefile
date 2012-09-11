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
  library/converter$(EXEEXT) cprover_library.inc \
  file_converter$(EXEEXT) \
  gcc_builtin_headers_generic.inc gcc_builtin_headers_ia32.inc \
  arm_builtin_headers.inc cw_builtin_headers.inc

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

file_converter$(EXEEXT): file_converter.cpp
	$(LINKBIN)

.PHONY: library_check

library_check:
	for f in library/*.c ; do \
		[ $$f = "library/windows.c" ] && [ "x$(EXEEXT)" = "x" ] && continue ; \
		[ $$f = "library/threads.c" ] && continue ; \
		$(CC) -S -Wall -pedantic -std=gnu99 -fno-builtin $$f -o __libcheck.s \
			-Wno-unused-label -Wno-implicit-function-declaration -Wno-uninitialized ; \
		ec=$$? ; \
		$(RM) __libcheck.s ; \
		[ $$ec -eq 0 ] || exit $$ec ; \
	done
	
cprover_library.inc: library/converter$(EXEEXT) library/*.c
	cat library/*.c | library/converter$(EXEEXT) > $@

gcc_builtin_headers_ia32.inc: gcc_builtin_headers_ia32.h file_converter$(EXEEXT)
	./file_converter$(EXEEXT) < gcc_builtin_headers_ia32.h > $@

gcc_builtin_headers_generic.inc: gcc_builtin_headers_generic.h file_converter$(EXEEXT)
	./file_converter$(EXEEXT) < gcc_builtin_headers_generic.h > $@

arm_builtin_headers.inc: arm_builtin_headers.h file_converter$(EXEEXT)
	./file_converter$(EXEEXT) < arm_builtin_headers.h > $@

cw_builtin_headers.inc: cw_builtin_headers.h file_converter$(EXEEXT)
	./file_converter$(EXEEXT) < cw_builtin_headers.h > $@

cprover_library.cpp: cprover_library.inc

internal_additions$(OBJEXT): gcc_builtin_headers_generic.inc
internal_additions$(OBJEXT): gcc_builtin_headers_ia32.inc
internal_additions$(OBJEXT): arm_builtin_headers.inc
internal_additions$(OBJEXT): cw_builtin_headers.inc

###############################################################################

ansi-c$(LIBEXT): $(OBJ) 
	$(LINKLIB)

