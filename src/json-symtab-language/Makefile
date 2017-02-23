SRC = json_symtab_language.cpp \
	json_symbol_table.cpp \
	json_symbol.cpp 

INCLUDES= -I ..

include ../config.inc
include ../common

CLEANFILES = json-symtab-language$(LIBEXT)

all: json-symtab-language$(LIBEXT)

###############################################################################

json-symtab-language$(LIBEXT): $(OBJ)
	$(LINKLIB)
