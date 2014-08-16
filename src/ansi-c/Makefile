SRC = c_typecast.cpp ansi_c_y.tab.cpp ansi_c_lex.yy.cpp ansi_c_parser.cpp \
      expr2c.cpp ansi_c_language.cpp c_sizeof.cpp ansi_c_scope.cpp \
      c_types.cpp trans_unit.cpp ansi_c_typecheck.cpp \
      c_preprocess.cpp c_storage_spec.cpp \
      c_typecheck_base.cpp c_typecheck_initializer.cpp \
      c_typecheck_typecast.cpp c_typecheck_code.cpp \
      c_typecheck_expr.cpp c_typecheck_type.cpp string_constant.cpp \
      c_qualifiers.cpp c_typecheck_argc_argv.cpp ansi_c_parse_tree.cpp \
      preprocessor_line.cpp ansi_c_convert_type.cpp \
      type2name.cpp cprover_library.cpp anonymous_member.cpp \
      printf_formatter.cpp ansi_c_internal_additions.cpp padding.cpp \
      ansi_c_declaration.cpp designator.cpp \
      literals/parse_float.cpp literals/unescape_string.cpp \
      literals/convert_float_literal.cpp \
      literals/convert_character_literal.cpp \
      literals/convert_integer_literal.cpp \
      literals/convert_string_literal.cpp

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
	clang_builtin_headers.inc gcc_builtin_headers_ia32-2.inc

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
  platform_unavail = library/err.c library/threads.c
else
  platform_unavail = library/threads.c
endif
library_check: library/*.c
	for f in $(filter-out $(platform_unavail), $^) ; do \
		cp $$f __libcheck.c ; \
		sed -i 's/__builtin_[^v]/s&/' __libcheck.c ; \
		sed -i 's/__sync_/s&/' __libcheck.c ; \
		sed -i 's/__noop/s&/' __libcheck.c ; \
		$(CC) -std=gnu99 -E -include library/cprover.h -D__CPROVER_bool=_Bool \
			-D__CPROVER_thread_local=__thread -DLIBRARY_CHECK -o __libcheck.i __libcheck.c ; \
		$(CC) -S -Wall -Werror -pedantic -Wextra -std=gnu99 __libcheck.i -o __libcheck.s \
			-Wno-unused-label -Wno-uninitialized ; \
		ec=$$? ; \
		$(RM) __libcheck.s __libcheck.i __libcheck.c ; \
		[ $$ec -eq 0 ] || exit $$ec ; \
	done
	touch $@
	
cprover_library.inc: library/converter$(EXEEXT) library/*.c
	cat library/*.c | library/converter$(EXEEXT) > $@

%.inc: %.h file_converter$(EXEEXT)
	./file_converter$(EXEEXT) < $< > $@

cprover_library.cpp: cprover_library.inc

ansi_c_internal_additions$(OBJEXT): gcc_builtin_headers_generic.inc
ansi_c_internal_additions$(OBJEXT): gcc_builtin_headers_ia32.inc
ansi_c_internal_additions$(OBJEXT): gcc_builtin_headers_ia32-2.inc
ansi_c_internal_additions$(OBJEXT): gcc_builtin_headers_alpha.inc
ansi_c_internal_additions$(OBJEXT): gcc_builtin_headers_arm.inc
ansi_c_internal_additions$(OBJEXT): gcc_builtin_headers_mips.inc
ansi_c_internal_additions$(OBJEXT): gcc_builtin_headers_power.inc
ansi_c_internal_additions$(OBJEXT): arm_builtin_headers.inc
ansi_c_internal_additions$(OBJEXT): cw_builtin_headers.inc
ansi_c_internal_additions$(OBJEXT): clang_builtin_headers.inc

generated_files: cprover_library.inc gcc_builtin_headers_generic.inc \
	gcc_builtin_headers_ia32.inc gcc_builtin_headers_alpha.inc \
	gcc_builtin_headers_arm.inc gcc_builtin_headers_mips.inc \
	gcc_builtin_headers_power.inc arm_builtin_headers.inc \
	cw_builtin_headers.inc ansi_c_y.tab.cpp ansi_c_lex.yy.cpp \
	ansi_c_y.tab.h clang_builtin_headers.inc gcc_builtin_headers_ia32-2.inc

###############################################################################

ansi-c$(LIBEXT): $(OBJ) 
	$(LINKLIB)

