SRC = goto_inspect_main.cpp \
      goto_inspect_parse_options.cpp \
      # Empty last line

OBJ += ../big-int/big-int$(LIBEXT) \
       ../linking/linking$(LIBEXT) \
       ../langapi/langapi$(LIBEXT) \
       ../goto-programs/goto-programs$(LIBEXT) \
       ../util/util$(LIBEXT) \
       # Empty last line

INCLUDES= -I ..

LIBS =

CLEANFILES = goto-inspect$(EXEEXT) goto-inspect$(LIBEXT)

include ../config.inc
include ../common

all: goto-inspect$(EXEEXT)

###############################################################################

goto-inspect$(EXEEXT): $(OBJ)
	$(LINKBIN)

.PHONY: goto-inspect-mac-signed

goto-inspect-mac-signed: goto-inspect$(EXEEXT)
	codesign -v -s $(OSX_IDENTITY) goto-inspect$(EXEEXT)
