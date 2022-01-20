SRC = c_defines.cpp \
      c_lex.yy.cpp \
      c_wrangler.cpp \
      crangler_main.cpp \
      crangler_parse_options.cpp \
      cscanner.cpp \
      ctokenit.cpp \
      mini_c_parser.cpp \
      # Empty last line

OBJ += ../big-int/big-int$(LIBEXT) \
       ../json/json$(LIBEXT) \
       ../util/util$(LIBEXT)

INCLUDES= -I ..

include ../config.inc
include ../../$(CPROVER_DIR)/src/common

CLEANFILES = crangler$(LIBEXT) \
  c_lex.yy.cpp \
  crangler$(EXEEXT)

all: crangler$(EXEEXT)

###############################################################################

c_lex.yy.cpp: scanner.l
	$(LEX) -Pyyc -o$@ scanner.l

###############################################################################

generated_files: c_lex.yy.cpp

###############################################################################

crangler$(EXEEXT): $(OBJ)
	$(LINKBIN)
