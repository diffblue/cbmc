SRC = \
  goto_harness_main.cpp \
  goto_harness_parse_options.cpp \
  # Empty last line

OBJ += \
  ../util/util$(LIBEXT) \
  # Empty last line

INCLUDES= -I ..

LIBS =

CLEANFILES = goto-harness$(EXEEXT)

include ../config.inc
include ../common

all: goto-harness$(EXEEXT)

###############################################################################

goto-harness$(EXEEXT): $(OBJ)
	$(LINKBIN)

.PHONY: goto-harness-mac-signed

goto-harness-mac-signed: goto-harness$(EXEEXT)
	codesign -v -s $(OSX_IDENTITY) goto-harness$(EXEEXT)
