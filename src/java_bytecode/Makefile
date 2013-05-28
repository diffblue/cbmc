SRC = java_bytecode_language.cpp java_bytecode_parse_tree.cpp \
      java_bytecode_typecheck.cpp javap_parse.cpp

INCLUDES= -I ..

include ../config.inc
include ../common

CLEANFILES = java_bytecode$(LIBEXT)

all: java_bytecode$(LIBEXT)

###############################################################################

java_bytecode$(LIBEXT): $(OBJ) 
	$(LINKLIB)

