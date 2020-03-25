SRC = janalyzer_main.cpp \
      janalyzer_parse_options.cpp \
      # Empty last line

OBJ += ../$(CPROVER_DIR)/src/ansi-c/ansi-c$(LIBEXT) \
      ../java_bytecode/java_bytecode$(LIBEXT) \
      ../$(CPROVER_DIR)/src/linking/linking$(LIBEXT) \
      ../$(CPROVER_DIR)/src/big-int/big-int$(LIBEXT) \
      ../$(CPROVER_DIR)/src/goto-programs/goto-programs$(LIBEXT) \
      ../$(CPROVER_DIR)/src/analyses/analyses$(LIBEXT) \
      ../$(CPROVER_DIR)/src/pointer-analysis/pointer-analysis$(LIBEXT) \
      ../$(CPROVER_DIR)/src/langapi/langapi$(LIBEXT) \
      ../$(CPROVER_DIR)/src/json/json$(LIBEXT) \
      ../$(CPROVER_DIR)/src/solvers/solvers$(LIBEXT) \
      ../$(CPROVER_DIR)/src/util/util$(LIBEXT) \
      ..//miniz/miniz$(OBJEXT) \
      ../$(CPROVER_DIR)/src/goto-analyzer/static_show_domain$(OBJEXT) \
      ../$(CPROVER_DIR)/src/goto-analyzer/static_simplifier$(OBJEXT) \
      ../$(CPROVER_DIR)/src/goto-analyzer/static_verifier$(OBJEXT) \
      ../$(CPROVER_DIR)/src/goto-analyzer/taint_analysis$(OBJEXT) \
      ../$(CPROVER_DIR)/src/goto-analyzer/taint_parser$(OBJEXT) \
      ../$(CPROVER_DIR)/src/goto-analyzer/unreachable_instructions$(OBJEXT) \
      # Empty last line

INCLUDES= -I .. -I ../$(CPROVER_DIR)/src

LIBS =

include ../config.inc
include ../$(CPROVER_DIR)/src/config.inc
include ../$(CPROVER_DIR)/src/common

CLEANFILES = janalyzer$(EXEEXT)

all: janalyzer$(EXEEXT)

ifneq ($(wildcard ../jsil/Makefile),)
  OBJ += ../jsil/jsil$(LIBEXT)
  CP_CXXFLAGS += -DHAVE_JSIL
endif

###############################################################################

janalyzer$(EXEEXT): $(OBJ)
	$(LINKBIN)

.PHONY: janalyzer-mac-signed

janalyzer-mac-signed: janalyzer$(EXEEXT)
	strip janalyzer$(EXEEXT) ; codesign -v -s $(OSX_IDENTITY) janalyzer$(EXEEXT)
