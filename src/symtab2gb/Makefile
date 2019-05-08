SRC = \
  symtab2gb_main.cpp \
  symtab2gb_parse_options.cpp \
  # Empty last line

OBJ += \
  ../util/util$(LIBEXT) \
  ../goto-programs/goto-programs$(LIBEXT) \
  ../big-int/big-int$(LIBEXT) \
  ../langapi/langapi$(LIBEXT) \
  ../linking/linking$(LIBEXT) \
  ../json/json$(LIBEXT) \
  ../json-symtab-language/json-symtab-language$(LIBEXT) \
  # Empty last line

INCLUDES= -I ..

LIBS =

CLEANFILES = symtab2gb$(EXEEXT)

include ../config.inc
include ../common

all: symtab2gb$(EXEEXT)

###############################################################################

symtab2gb$(EXEEXT): $(OBJ)
	$(LINKBIN)

.PHONY: symtab2gb-mac-signed

symtab2gb-mac-signed: symtab2gb$(EXEEXT)
	codesign -v -s $(OSX_IDENTITY) symtab2gb2$(EXEEXT)
