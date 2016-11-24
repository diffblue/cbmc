SRC = clobber_main.cpp clobber_parse_options.cpp

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
       ../goto-symex/rewrite_union$(OBJEXT) \
       ../pointer-analysis/dereference$(OBJEXT) \
       ../goto-instrument/dump_c$(OBJEXT) \
       ../goto-instrument/goto_program2code$(OBJEXT)

INCLUDES= -I ..

LIBS =

include ../config.inc
include ../common

CLEANFILES = clobber$(EXEEXT)

all: clobber$(EXEEXT)

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

clobber$(EXEEXT): $(OBJ)
	$(LINKBIN)

.PHONY: clobber-mac-signed

clobber-mac-signed: cbmc$(EXEEXT)
	strip clobber$(EXEEXT) ; codesign -v -s $(OSX_IDENTITY) clobber$(EXEEXT)

