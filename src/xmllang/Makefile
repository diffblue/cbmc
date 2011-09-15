SRC = xml_language.cpp xml_parser.cpp y.tab.cpp lex.yy.cpp xml_typecheck.cpp \
      xml_parse_tree.cpp

INCLUDES= -I .. -I ../util

include ../config.inc
include ../common

CLEANFILES =xmllang$(LIBEXT) y.tab.h y.tab.cpp lex.yy.cpp y.tab.cpp.output y.output

all: xmllang$(LIBEXT)

###############################################################################

xmllang$(LIBEXT): $(OBJ)
	$(LINKLIB)

y.tab.cpp: parser.y
	$(YACC) $(YFLAGS) $$flags -pyyxml -d parser.y -o y.tab.cpp

y.tab.h: y.tab.cpp
	if [ -e y.tab.hpp ] ; then mv y.tab.hpp y.tab.h ; else \
        mv y.tab.cpp.h y.tab.h ; fi

lex.yy.cpp: scanner.l
	$(LEX) -Pyyxml -olex.yy.cpp scanner.l

# extra dependencies
y.tab$(OBJEXT): y.tab.cpp y.tab.h
lex.yy$(OBJEXT): y.tab.cpp lex.yy.cpp y.tab.h

