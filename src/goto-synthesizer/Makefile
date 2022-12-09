SRC = goto_synthesizer_languages.cpp \
      goto_synthesizer_main.cpp \
      goto_synthesizer_parse_options.cpp \
      # Empty last line

OBJ += ../ansi-c/ansi-c$(LIBEXT) \
      ../cpp/cpp$(LIBEXT) \
      ../linking/linking$(LIBEXT) \
      ../big-int/big-int$(LIBEXT) \
      ../goto-checker/goto-checker$(LIBEXT) \
      ../goto-programs/goto-programs$(LIBEXT) \
      ../langapi/langapi$(LIBEXT) \
      ../util/util$(LIBEXT) \
      ../json/json$(LIBEXT) \
      # Empty last line

INCLUDES= -I ..

LIBS =

CLEANFILES = goto-synthesizer$(EXEEXT) goto-synthesizer$(LIBEXT)

include ../config.inc
include ../common

all: goto-synthesizer$(EXEEXT)

###############################################################################

goto-synthesizer$(EXEEXT): $(OBJ)
	$(LINKBIN)

.PHONY: goto-synthesizer-mac-signed

goto-synthesizer-mac-signed: goto-synthesizer$(EXEEXT)
	codesign -v -s $(OSX_IDENTITY) goto-synthesizer$(EXEEXT)
