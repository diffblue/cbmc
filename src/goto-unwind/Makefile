SRC = src/goto_unwind_main.cpp \
			src/goto_unwind_parse_options.cpp \
			# Empty last line

OBJ += ../goto-programs/goto-programs$(LIBEXT) \
			 ../big-int/big-int$(LIBEXT) \
			 ../ansi-c/ansi-c$(LIBEXT) \
			 ../cpp/cpp$(LIBEXT) \
       ../util/util$(LIBEXT) \
			 ../langapi/langapi$(LIBEXT) \
			 ../analyses/analyses$(LIBEXT) \
			 ../linking/linking$(LIBEXT) \
			 ../goto-instrument/unwind$(OBJEXT) \
			 ../goto-instrument/unwindset$(OBJEXT) \
       # Empty last line

INCLUDES= -I ..

LIBS =

CLEANFILES = goto-unwind$(EXEEXT)

include ../config.inc
include ../common

all: goto-unwind$(EXEEXT)

###############################################################################

goto-unwind$(EXEEXT): $(OBJ)
	$(LINKBIN)

.PHONY: goto-unwind-mac-signed

goto-unwind-mac-signed: goto-unwind(EXEEXT)
	codesign -v -s $(OSX_IDENTITY) goto-unwind(EXEEXT)
