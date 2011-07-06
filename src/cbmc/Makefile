SRC = main.cpp parseoptions.cpp bmc.cpp dimacs.cpp languages.cpp \
      bv_cbmc.cpp symex_bmc.cpp show_vcc.cpp cbmc_solvers.cpp \
      xml_interface.cpp \
      counterexample_beautification.cpp \
      counterexample_beautification_greedy.cpp \
      counterexample_beautification_pbs.cpp

OBJ = $(SRC:.cpp=$(OBJEXT)) \
      ../ansi-c/ansi-c$(LIBEXT) \
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

all: cbmc$(EXEEXT)

ifdef MODULE_BV_REFINEMENT
  OBJ += ../bv_refinement/bv_refinement$(LIBEXT)
  CXXFLAGS += -DHAVE_BV_REFINEMENT
endif

ifdef MODULE_CPP
  OBJ += ../cpp/cpp$(LIBEXT)
  CXXFLAGS += -DHAVE_CPP
endif

ifdef MODULE_JAVA
  OBJ += ../java/java$(LIBEXT)
  CXXFLAGS += -DHAVE_JAVA
endif

ifdef MODULE_SPECC
  OBJ += ../specc/specc$(LIBEXT)
  CXXFLAGS += -DHAVE_SPECC
endif

ifdef MODULE_PHP
  OBJ += ../php/php$(LIBEXT)
  CXXFLAGS += -DHAVE_PHP
endif

###############################################################################

cbmc$(EXEEXT): $(OBJ)
	$(LINKBIN) $(OBJ)

clean:
	rm -f $(SRC:.cpp=$(OBJEXT)) cbmc$(EXEEXT)
