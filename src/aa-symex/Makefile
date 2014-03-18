SRC = symex_main.cpp symex_parseoptions.cpp path_search.cpp

OBJ += ../ansi-c/ansi-c$(LIBEXT) \
       ../linking/linking$(LIBEXT) \
       ../big-int/big-int$(LIBEXT) \
       ../goto-programs/goto-programs$(LIBEXT) \
       ../analyses/analyses$(LIBEXT) \
       ../langapi/langapi$(LIBEXT) \
       ../xmllang/xmllang$(LIBEXT) \
       ../assembler/assembler$(LIBEXT) \
       ../solvers/solvers$(LIBEXT) \
       ../util/util$(LIBEXT) \
       ../goto-symex/adjust_float_expressions$(OBJEXT) \
       ../pointer-analysis/dereference$(OBJEXT) \
       ../aa-path-symex/aa-path-symex$(LIBEXT)

INCLUDES= -I ..

LIBS =

include ../config.inc
include ../common

CLEANFILES = symex$(EXEEXT)

all: symex$(EXEEXT)

ifneq ($(wildcard ../bv_refinement/Makefile),)
  OBJ += ../bv_refinement/bv_refinement$(LIBEXT)
  CP_CXXFLAGS += -DHAVE_BV_REFINEMENT
endif

ifneq ($(wildcard ../cpp/Makefile),)
  OBJ += ../cpp/cpp$(LIBEXT)
  CP_CXXFLAGS += -DHAVE_CPP
endif

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

symex$(EXEEXT): $(OBJ)
	$(LINKBIN)

.PHONY: symex-mac-signed

symex-mac-signed: cbmc$(EXEEXT)
	strip symex$(EXEEXT) ; codesign -v -s $(OSX_IDENTITY) symex$(EXEEXT)

