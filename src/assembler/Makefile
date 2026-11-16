SRC = asm_approximation.cpp \
      asm_lowering.cpp \
      asm_operands.cpp \
      asm_semantics.cpp \
      asm_template.cpp \
      asm_x86.cpp \
      assembler_lex.yy.cpp \
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

generated_files: assembler_lex.yy.cpp

###############################################################################

assembler$(LIBEXT): $(OBJ)
	$(LINKLIB)
