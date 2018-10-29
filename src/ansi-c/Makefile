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
      builtin_factory.cpp \
      c_misc.cpp \
      c_nondet_symbol_factory.cpp \
      c_object_factory_parameters.cpp \
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
      gcc_types.cpp \
      literals/convert_character_literal.cpp \
      literals/convert_float_literal.cpp \
      literals/convert_integer_literal.cpp \
      literals/convert_string_literal.cpp \
      literals/parse_float.cpp \
      literals/unescape_string.cpp \
      padding.cpp \
      preprocessor_line.cpp \
      type2name.cpp \
      # Empty last line

INCLUDES= -I ..

include ../config.inc
include ../common

BUILTIN_FILES = \
  arm_builtin_headers.inc \
  clang_builtin_headers.inc \
  cprover_builtin_headers.inc \
  cw_builtin_headers.inc \
  gcc_builtin_headers_alpha.inc \
  gcc_builtin_headers_arm.inc \
  gcc_builtin_headers_generic.inc \
  gcc_builtin_headers_ia32-2.inc \
  gcc_builtin_headers_ia32-3.inc \
  gcc_builtin_headers_ia32-4.inc \
  gcc_builtin_headers_ia32.inc \
  gcc_builtin_headers_math.inc \
  gcc_builtin_headers_mem_string.inc \
  gcc_builtin_headers_mips.inc \
  gcc_builtin_headers_omp.inc \
  gcc_builtin_headers_power.inc \
  gcc_builtin_headers_tm.inc \
  gcc_builtin_headers_types.inc \
  gcc_builtin_headers_ubsan.inc \
  windows_builtin_headers.inc

CLEANFILES = ansi-c$(LIBEXT) \
  ansi_c_y.tab.h ansi_c_y.tab.cpp ansi_c_lex.yy.cpp ansi_c_y.tab.cpp.output \
  ansi_c_y.output \
  library/converter$(EXEEXT) cprover_library.inc \
  file_converter$(EXEEXT) library_check \
  $(BUILTIN_FILES)

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
	./library_check.sh $(CC) $(filter-out $(platform_unavail), $^)
	touch $@

cprover_library.inc: library/converter$(EXEEXT) library/*.c
	cat library/*.c | library/converter$(EXEEXT) > $@

%.inc: %.h file_converter$(EXEEXT)
	./file_converter$(EXEEXT) < $< > $@

ansi_c_internal_additions$(OBJEXT): $(BUILTIN_FILES)

generated_files: \
        ansi_c_y.tab.cpp ansi_c_lex.yy.cpp ansi_c_y.tab.h \
        cprover_library.inc \
        $(BUILTIN_FILES)

###############################################################################

ansi-c$(LIBEXT): $(OBJ)
	$(LINKLIB)
