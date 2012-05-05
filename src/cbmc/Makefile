SRC = main.cpp parseoptions.cpp bmc.cpp dimacs.cpp languages.cpp \
      bv_cbmc.cpp symex_bmc.cpp show_vcc.cpp cbmc_solvers.cpp \
      xml_interface.cpp cover.cpp \
      counterexample_beautification.cpp \
      counterexample_beautification_greedy.cpp \
      counterexample_beautification_pbs.cpp

OBJ += ../ansi-c/ansi-c$(LIBEXT) \
      ../big-int/bigint$(OBJEXT) \
      ../goto-programs/goto-programs$(LIBEXT) \
      ../goto-symex/goto-symex$(LIBEXT) \
      ../pointer-analysis/pointer-analysis$(LIBEXT) \
      ../langapi/langapi$(LIBEXT) \
      ../xmllang/xmllang$(LIBEXT) \
      ../solvers/solvers$(LIBEXT) \
      ../util/util$(LIBEXT)

INCLUDES= -I .. -I ../util

LIBS =

include ../config.inc
include ../common

CLEANFILES = cbmc$(EXEEXT)

all: cbmc$(EXEEXT)

ifneq ($(wildcard ../bv_refinement/Makefile),)
  OBJ += ../bv_refinement/bv_refinement$(LIBEXT)
  CP_CXXFLAGS += -DHAVE_BV_REFINEMENT
endif

ifneq ($(wildcard ../cpp/Makefile),)
  OBJ += ../cpp/cpp$(LIBEXT)
  CP_CXXFLAGS += -DHAVE_CPP
endif

ifneq ($(wildcard ../java/Makefile),)
  OBJ += ../java/java$(LIBEXT)
  CP_CXXFLAGS += -DHAVE_JAVA
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

cbmc$(EXEEXT): $(OBJ)
	$(LINKBIN)

cbmc-mac-signed: cbmc$(EXEEXT)
	codesign -v -s $(OSX_IDENTITY) cbmc$(EXEEXT)

