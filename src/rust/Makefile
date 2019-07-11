SRC = expr2rust.cpp \
      rust_convert.cpp \
      rust_entry_point.cpp \
      rust_internal_additions.cpp \
      rust_language.cpp \
      rust_lex.yy.cpp \
      rust_parse_tree.cpp \
      rust_parseassert.cpp \
      rust_parser.cpp \
      rust_typecheck.cpp \
      rust_types.cpp \
      rust_y.tab.cpp \
      # Empty last line

	  
INCLUDES= -I ..

include ../config.inc
include ../common

CLEANFILES=rust$(LIBEXT) rust_y.tab.h rust_y.tab.cpp rust_lex.yy.cpp \
           rust_y.tab.cpp.output rust_y.output

all: rust$(LIBEXT)

###############################################################################

rust$(LIBEXT): $(OBJ)
	$(LINKLIB)

rust_y.tab.cpp: parser.y
	$(YACC) $(YFLAGS) $$flags -pyyrust -d -t parser.y --defines=rust_y.tab.h -o $@

rust_y.tab.h: rust_y.tab.cpp

rust_lex.yy.cpp: scanner.l
	$(LEX) -Pyyrust -o$@ -d scanner.l

generated_files: rust_lex.yy.cpp rust_y.tab.cpp rust_y.tab.h

# extra dependencies
rust_parser$(OBJEXT): rust_y.tab.h
rust_parseassert$(OBJEXT): rust_y.tab.h
rust_language$(OBJEXT): rust_y.tab.h
rust_y.tab$(OBJEXT): rust_y.tab.cpp rust_y.tab.h
rust_lex.yy$(OBJEXT): rust_y.tab.cpp rust_lex.yy.cpp rust_y.tab.h
