SRC = goto_contracts_languages.cpp \
      goto_contracts_main.cpp \
      goto_contracts_parse_options.cpp \
      # Empty last line

OBJ += ../ansi-c/ansi-c$(LIBEXT) \
      ../cpp/cpp$(LIBEXT) \
      ../big-int/big-int$(LIBEXT) \
      ../goto-programs/goto-programs$(LIBEXT) \
      ../langapi/langapi$(LIBEXT) \
      ../util/util$(LIBEXT) \
      ../json/json$(LIBEXT) \
      # Empty last line

INCLUDES= -I ..

LIBS =

CLEANFILES = goto-contracts$(EXEEXT) goto-contracts$(LIBEXT)

include ../config.inc
include ../common

all: goto-contracts$(EXEEXT)

###############################################################################

goto-contracts$(EXEEXT): $(OBJ)
	$(LINKBIN)

.PHONY: goto-contracts-mac-signed

goto-contracts-mac-signed: goto-contracts$(EXEEXT)
	codesign -v -s $(OSX_IDENTITY) goto-contracts$(EXEEXT)
