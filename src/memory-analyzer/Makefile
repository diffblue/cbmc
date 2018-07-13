SRC = analyze_symbol.cpp\
			gdb_api.cpp \
			memory_analyzer_main.cpp \
			memory_analyzer_parse_options.cpp
      # Empty last line

INCLUDES= -I ..

LIBS = \
	../ansi-c/ansi-c$(LIBEXT) \
	../goto-programs/goto-programs$(LIBEXT) \
	../linking/linking$(LIBEXT) \
	../util/util$(LIBEXT) \
	../big-int/big-int$(LIBEXT) \
	../langapi/langapi$(LIBEXT)

	

CLEANFILES = memory-analyzer$(EXEEXT) 

include ../config.inc
include ../common

all: memory-analyzer$(EXEEXT)



###############################################################################

memory-analyzer$(EXEEXT): $(OBJ)
	$(LINKBIN)


.PHONY: memory-analyser-mac-signed

memory-analyser-mac-signed: memory-analyzer$(EXEEXT)
	codesign -v -s $(OSX_IDENTITY) memory-analyzer$(EXEEXT)
