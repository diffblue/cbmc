SRC = assembler_lex.yy.cpp \
      assembler_parser.cpp \
      remove_asm.cpp \
      # Empty last line
INCLUDES= -I ..

include ../config.inc
include ../common

CLEANFILES = assembler$(LIBEXT) \
  assembler_lex.yy.cpp

all: assembler$(LIBEXT)

###############################################################################

assembler_lex.yy.cpp: scanner.l
	$(LEX) -Pyyassembler -o$@ scanner.l
	$(SED) -e's,struct yyguts_t,struct yyasmguts_t,' <$@ >$@.tmp && mv $@.tmp $@

generated_files: assembler_lex.yy.cpp

###############################################################################

assembler$(LIBEXT): $(OBJ)
	$(LINKLIB)
