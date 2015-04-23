SRC = mm_y.tab.cpp mm_lex.yy.cpp mmcc_main.cpp mm_parser.cpp \
      mmcc_parse_options.cpp mm2cpp.cpp

OBJ += ../big-int/big-int$(LIBEXT) \
      ../util/util$(LIBEXT)

INCLUDES= -I ..

include ../config.inc
include ../common

CLEANFILES = memory_models$(LIBEXT) \
  mm_y.tab.h mm_y.tab.cpp mm_lex.yy.cpp mm_y.tab.cpp.output mm_y.output

all: mmcc$(EXEEXT)

###############################################################################

mm_y.tab.cpp: parser.y
	$(YACC) $(YFLAGS) $$flags -pyymm -d parser.y -o $@

mm_y.tab.h: mm_y.tab.cpp
	if [ -e mm_y.tab.hpp ] ; then mv mm_y.tab.hpp mm_y.tab.h ; else \
        mv mm_y.tab.cpp.h mm_y.tab.h ; fi

mm_lex.yy.cpp: scanner.l
	$(LEX) -Pyymm -o$@ scanner.l

# extra dependencies
mm_y.tab$(OBJEXT): mm_y.tab.cpp mm_y.tab.h
mm_lex.yy$(OBJEXT): mm_y.tab.cpp mm_lex.yy.cpp mm_y.tab.h

###############################################################################

generated_files: mm_y.tab.cpp mm_lex.yy.cpp mm_y.tab.h

###############################################################################

mmcc$(EXEEXT): $(OBJ) 
	$(LINKBIN)

