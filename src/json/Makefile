SRC = json_lex.yy.cpp \
      json_parser.cpp \
      json_y.tab.cpp \
      # Empty last line
INCLUDES= -I ..

include ../config.inc
include ../common

CLEANFILES=json$(LIBEXT) json_y.tab.h json_y.tab.cpp json_lex.yy.cpp \
           json_y.tab.cpp.output json_y.output

all: json$(LIBEXT)

###############################################################################

json$(LIBEXT): $(OBJ)
	$(LINKLIB)

json_y.tab.cpp: parser.y
	$(YACC) $(YFLAGS) $$flags -pyyjson -d parser.y -o $@

json_y.tab.h: json_y.tab.cpp
	if [ -e json_y.tab.hpp ] ; then mv json_y.tab.hpp $@ ; else \
        mv json_y.tab.cpp.h $@ ; fi

json_lex.yy.cpp: scanner.l
	$(LEX) -Pyyjson -o$@ scanner.l

generated_files: json_lex.yy.cpp json_y.tab.cpp json_y.tab.h

# extra dependencies
json_y.tab$(OBJEXT): json_y.tab.cpp json_y.tab.h
json_lex.yy$(OBJEXT): json_y.tab.cpp json_lex.yy.cpp json_y.tab.h
