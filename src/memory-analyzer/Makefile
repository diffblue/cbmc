SRC = analyze_symbol.cpp\
			gdb_api.cpp \
			memory_analyzer_main.cpp \
			memory_analyzer_parse_options.cpp
      # Empty last line

INCLUDES= -I ..

LIBS = \
	../ansi-c/ansi-c.a \
	../goto-programs/goto-programs.a \
	../linking/linking.a \
	../util/util.a \
	../big-int/big-int.a \
	../langapi/langapi.a

	

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
