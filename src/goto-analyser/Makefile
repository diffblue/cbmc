SRC = goto_analyser_main.cpp goto_analyser_parse_options.cpp \
      taint_parser.cpp taint_analysis.cpp

OBJ += ../ansi-c/ansi-c$(LIBEXT) \
      ../linking/linking$(LIBEXT) \
      ../big-int/big-int$(LIBEXT) \
      ../goto-programs/goto-programs$(LIBEXT) \
      ../analyses/analyses$(LIBEXT) \
      ../langapi/langapi$(LIBEXT) \
      ../json/json$(LIBEXT) \
      ../assembler/assembler$(LIBEXT) \
      ../util/util$(LIBEXT)

INCLUDES= -I ..

LIBS =

include ../config.inc
include ../common

CLEANFILES = goto-analyser$(EXEEXT)

all: goto-analyser$(EXEEXT)

ifneq ($(wildcard ../cpp/Makefile),)
  OBJ += ../cpp/cpp$(LIBEXT)
  CP_CXXFLAGS += -DHAVE_CPP
endif

ifneq ($(wildcard ../java_bytecode/Makefile),)
  OBJ += ../java_bytecode/java_bytecode$(LIBEXT)
  CP_CXXFLAGS += -DHAVE_JAVA_BYTECODE
  ifneq ($(LIBZIPLIB),)
    LIBS += -L $(LIBZIPLIB) -lzip -lz
  endif
endif

ifneq ($(wildcard ../specc/Makefile),)
  OBJ += ../specc/specc$(LIBEXT)
  CP_CXXFLAGS += -DHAVE_SPECC
endif

ifneq ($(wildcard ../php/Makefile),)
  OBJ += ../php/php$(LIBEXT)
  CP_CXXFLAGS += -DHAVE_PHP
endif

###############################################################################

goto-analyser$(EXEEXT): $(OBJ)
	$(LINKBIN)

.PHONY: goto-analyser-mac-signed

goto-analyser-mac-signed: goto-analyser$(EXEEXT)
	strip goto-analyser$(EXEEXT) ; codesign -v -s $(OSX_IDENTITY) goto-analyser$(EXEEXT)

