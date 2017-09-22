SRC = anonymous_member.cpp \
      ansi_c_convert_type.cpp \
      ansi_c_declaration.cpp \
      ansi_c_entry_point.cpp \
      ansi_c_internal_additions.cpp \
      ansi_c_language.cpp \
      ansi_c_lex.yy.cpp \
      ansi_c_parse_tree.cpp \
      ansi_c_parser.cpp \
      ansi_c_scope.cpp \
      ansi_c_typecheck.cpp \
      ansi_c_y.tab.cpp \
      c_misc.cpp \
      c_nondet_symbol_factory.cpp \
      c_preprocess.cpp \
      c_qualifiers.cpp \
      c_storage_spec.cpp \
      c_typecast.cpp \
      c_typecheck_argc_argv.cpp \
      c_typecheck_base.cpp \
      c_typecheck_code.cpp \
      c_typecheck_expr.cpp \
      c_typecheck_initializer.cpp \
      c_typecheck_type.cpp \
      c_typecheck_typecast.cpp \
      cprover_library.cpp \
      designator.cpp \
      expr2c.cpp \
      literals/convert_character_literal.cpp \
      literals/convert_float_literal.cpp \
      literals/convert_integer_literal.cpp \
      literals/convert_string_literal.cpp \
      literals/parse_float.cpp \
      literals/unescape_string.cpp \
      padding.cpp \
      preprocessor_line.cpp \
      printf_formatter.cpp \
      string_constant.cpp \
      type2name.cpp \
      # Empty last line

INCLUDES= -I ..

include ../config.inc
include ../common

CLEANFILES = ansi-c$(LIBEXT) \
  ansi_c_y.tab.h ansi_c_y.tab.cpp ansi_c_lex.yy.cpp ansi_c_y.tab.cpp.output \
  ansi_c_y.output \
  library/converter$(EXEEXT) cprover_library.inc \
  file_converter$(EXEEXT) library_check \
  gcc_builtin_headers_generic.inc gcc_builtin_headers_ia32.inc \
  arm_builtin_headers.inc cw_builtin_headers.inc \
  gcc_builtin_headers_arm.inc gcc_builtin_headers_alpha.inc \
  gcc_builtin_headers_mips.inc gcc_builtin_headers_power.inc \
	clang_builtin_headers.inc gcc_builtin_headers_ia32-2.inc \
  gcc_builtin_headers_math.inc gcc_builtin_headers_omp.inc \
  gcc_builtin_headers_tm.inc gcc_builtin_headers_ubsan.inc \
  gcc_builtin_headers_mem_string.inc \
  gcc_builtin_headers_ia32-3.inc gcc_builtin_headers_ia32-4.inc

all: ansi-c$(LIBEXT)

###############################################################################

ansi_c_y.tab.cpp: parser.y
	$(YACC) $(YFLAGS) $$flags -pyyansi_c -d parser.y -o $@

ansi_c_y.tab.h: ansi_c_y.tab.cpp
	if [ -e ansi_c_y.tab.hpp ] ; then mv ansi_c_y.tab.hpp ansi_c_y.tab.h ; else \
        mv ansi_c_y.tab.cpp.h ansi_c_y.tab.h ; fi

ansi_c_lex.yy.cpp: scanner.l
	$(LEX) -Pyyansi_c -o$@ scanner.l

# extra dependencies
ansi_c_y.tab$(OBJEXT): ansi_c_y.tab.cpp ansi_c_y.tab.h
ansi_c_lex.yy$(OBJEXT): ansi_c_y.tab.cpp ansi_c_lex.yy.cpp ansi_c_y.tab.h
cprover_library$(OBJEXT): cprover_library.inc

###############################################################################

library/converter$(EXEEXT): library/converter.cpp
	$(LINKNATIVE)

file_converter$(EXEEXT): file_converter.cpp
	$(LINKNATIVE)

ifeq ($(BUILD_ENV),MinGW)
  platform_unavail = library/java.io.c library/err.c library/threads.c
else
  platform_unavail = library/java.io.c library/threads.c
endif
library_check: library/*.c
	./library_check.sh $(filter-out $(platform_unavail), $^)
	touch $@

cprover_library.inc: library/converter$(EXEEXT) library/*.c
	cat library/*.c | library/converter$(EXEEXT) > $@

%.inc: %.h file_converter$(EXEEXT)
	./file_converter$(EXEEXT) < $< > $@

cprover_library.cpp: cprover_library.inc

ansi_c_internal_additions$(OBJEXT): gcc_builtin_headers_generic.inc
ansi_c_internal_additions$(OBJEXT): gcc_builtin_headers_ia32.inc
ansi_c_internal_additions$(OBJEXT): gcc_builtin_headers_ia32-2.inc
ansi_c_internal_additions$(OBJEXT): gcc_builtin_headers_ia32-3.inc
ansi_c_internal_additions$(OBJEXT): gcc_builtin_headers_ia32-4.inc
ansi_c_internal_additions$(OBJEXT): gcc_builtin_headers_alpha.inc
ansi_c_internal_additions$(OBJEXT): gcc_builtin_headers_arm.inc
ansi_c_internal_additions$(OBJEXT): gcc_builtin_headers_math.inc
ansi_c_internal_additions$(OBJEXT): gcc_builtin_headers_mem_string.inc
ansi_c_internal_additions$(OBJEXT): gcc_builtin_headers_mips.inc
ansi_c_internal_additions$(OBJEXT): gcc_builtin_headers_omp.inc
ansi_c_internal_additions$(OBJEXT): gcc_builtin_headers_power.inc
ansi_c_internal_additions$(OBJEXT): gcc_builtin_headers_tm.inc
ansi_c_internal_additions$(OBJEXT): gcc_builtin_headers_ubsan.inc
ansi_c_internal_additions$(OBJEXT): arm_builtin_headers.inc
ansi_c_internal_additions$(OBJEXT): cw_builtin_headers.inc
ansi_c_internal_additions$(OBJEXT): clang_builtin_headers.inc

generated_files: cprover_library.inc gcc_builtin_headers_generic.inc \
	gcc_builtin_headers_ia32.inc gcc_builtin_headers_alpha.inc \
	gcc_builtin_headers_arm.inc gcc_builtin_headers_mips.inc \
	gcc_builtin_headers_power.inc arm_builtin_headers.inc \
	cw_builtin_headers.inc ansi_c_y.tab.cpp ansi_c_lex.yy.cpp \
	ansi_c_y.tab.h clang_builtin_headers.inc gcc_builtin_headers_ia32-2.inc \
  gcc_builtin_headers_math.inc gcc_builtin_headers_omp.inc \
  gcc_builtin_headers_tm.inc gcc_builtin_headers_ubsan.inc \
  gcc_builtin_headers_mem_string.inc \
  gcc_builtin_headers_ia32-3.inc gcc_builtin_headers_ia32-4.inc

###############################################################################

ansi-c$(LIBEXT): $(OBJ)
	$(LINKLIB)
