SRC = change_impact.cpp \
      goto_diff_base.cpp \
      goto_diff_languages.cpp \
      goto_diff_main.cpp \
      goto_diff_parse_options.cpp \
      syntactic_diff.cpp \
      unified_diff.cpp \
      # Empty last line

OBJ += ../ansi-c/ansi-c$(LIBEXT) \
      ../cpp/cpp$(LIBEXT) \
      ../linking/linking$(LIBEXT) \
      ../big-int/big-int$(LIBEXT) \
      ../goto-programs/goto-programs$(LIBEXT) \
      ../assembler/assembler$(LIBEXT) \
      ../pointer-analysis/pointer-analysis$(LIBEXT) \
      ../analyses/analyses$(LIBEXT) \
      ../langapi/langapi$(LIBEXT) \
      ../xmllang/xmllang$(LIBEXT) \
      ../util/util$(LIBEXT) \
      ../solvers/solvers$(LIBEXT) \
      ../miniz/miniz$(OBJEXT) \
      ../json/json$(LIBEXT)

INCLUDES= -I ..

LIBS =

include ../config.inc
include ../common

CLEANFILES = goto-diff$(EXEEXT)

all: goto-diff$(EXEEXT)

CP_CXXFLAGS += -DCBMC_VERSION="\"$(CBMC_VERSION) ($(RELEASE_INFO))\""

ifneq ($(wildcard ../java_bytecode/Makefile),)
  OBJ += ../java_bytecode/java_bytecode$(LIBEXT)
  CP_CXXFLAGS += -DHAVE_JAVA_BYTECODE
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

goto-diff$(EXEEXT): $(OBJ)
	$(LINKBIN)

.PHONY: goto-diff-mac-signed

cbmc-mac-signed: goto-diff$(EXEEXT)
	strip goto-diff$(EXEEXT) ; codesign -v -s $(OSX_IDENTITY) goto-diff$(EXEEXT)
