SRC = expr2jsil.cpp \
      jsil_convert.cpp \
      jsil_entry_point.cpp \
      jsil_internal_additions.cpp \
      jsil_language.cpp \
      jsil_lex.yy.cpp \
      jsil_parse_tree.cpp \
      jsil_parser.cpp \
      jsil_typecheck.cpp \
      jsil_types.cpp \
      jsil_y.tab.cpp \
      # Empty last line

INCLUDES= -I ..

include ../config.inc
include ../common

CLEANFILES = jsil$(LIBEXT) \
	jsil_y.tab.h jsil_y.tab.cpp jsil_lex.yy.cpp \
	jsil_y.tab.cpp.output jsil_y.output

all: jsil$(LIBEXT)

###############################################################################

jsil$(LIBEXT): $(OBJ)
	$(LINKLIB)

jsil_y.tab.cpp: parser.y
	$(YACC) $(YFLAGS) $$flags -pyyjsil -d parser.y -o $@

jsil_y.tab.h: jsil_y.tab.cpp
	if [ -e jsil_y.tab.hpp ] ; then mv jsil_y.tab.hpp jsil_y.tab.h ; else \
        mv jsil_y.tab.cpp.h jsil_y.tab.h ; fi

jsil_lex.yy.cpp: scanner.l
	$(LEX) -Pyyjsil -o$@ scanner.l

generated_files: jsil_lex.yy.cpp jsil_y.tab.cpp jsil_y.tab.h

# extra dependencies
jsil_y.tab$(OBJEXT): jsil_y.tab.cpp jsil_y.tab.h
jsil_lex.yy$(OBJEXT): jsil_y.tab.cpp jsil_lex.yy.cpp jsil_y.tab.h
