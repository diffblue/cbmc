SRC = \
  goto_bmc_main.cpp \
  goto_bmc_parse_options.cpp \
  # Empty last line

OBJ += \
  ../libcprover-cpp/libcprover-cpp$(LIBEXT) \
  # Empty last line

INCLUDES= -I .. -I ../libcprover-cpp

LIBS =

CLEANFILES = goto-bmc$(EXEEXT)

include ../config.inc
include ../common

all: goto-bmc$(EXEEXT)

###############################################################################

goto-bmc$(EXEEXT): $(OBJ)
	$(LINKBIN)

.PHONY: goto-bmc-mac-signed

goto-bmc-mac-signed: goto-bmc$(EXEEXT)
	codesign -v -s $(OSX_IDENTITY) goto-bmc$(EXEEXT)
