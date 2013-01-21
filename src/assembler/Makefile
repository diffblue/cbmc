SRC = lex.yy.cpp assembler_parser.cpp

INCLUDES= -I .. -I ../util

include ../config.inc
include ../common

CLEANFILES = assembler$(LIBEXT) \
  lex.yy.cpp

all: assembler$(LIBEXT)

###############################################################################

lex.yy.cpp: scanner.l
	$(LEX) -Pyyassembler -o$@ scanner.l

###############################################################################

assembler$(LIBEXT): $(OBJ) 
	$(LINKLIB)

