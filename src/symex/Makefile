SRC = path_search.cpp \
      symex_cover.cpp \
      symex_main.cpp \
      symex_parse_options.cpp \
      # Empty last line

OBJ += ../ansi-c/ansi-c$(LIBEXT) \
       ../cpp/cpp$(LIBEXT) \
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
       ../goto-symex/rewrite_union$(OBJEXT) \
       ../pointer-analysis/dereference$(OBJEXT) \
       ../goto-instrument/cover$(OBJEXT) \
       ../path-symex/path-symex$(LIBEXT) \
       ../miniz/miniz$(OBJEXT) \
       ../json/json$(LIBEXT)

INCLUDES= -I ..

LIBS =

include ../config.inc
include ../common

CLEANFILES = symex$(EXEEXT)

all: symex$(EXEEXT)

ifeq ($(BUILD_ENV_),MSVC)
  CP_CXXFLAGS += /DCBMC_VERSION='"""$(CBMC_VERSION) ($(GIT_INFO))"""'
else
  CP_CXXFLAGS += -DCBMC_VERSION="\"$(CBMC_VERSION) ($(GIT_INFO))\""
endif

ifneq ($(wildcard ../bv_refinement/Makefile),)
  OBJ += ../bv_refinement/bv_refinement$(LIBEXT)
  CP_CXXFLAGS += -DHAVE_BV_REFINEMENT
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
