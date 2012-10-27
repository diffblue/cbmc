SRC = main.cpp parseoptions.cpp document_claims.cpp languages.cpp \
      uninitialized.cpp uninitialized_domain.cpp full_slicer.cpp \
      object_id.cpp show_locations.cpp points_to.cpp \
      alignment_checks.cpp race_check.cpp rw_set.cpp \
      weak_memory.cpp nondet_volatile.cpp interrupt.cpp \
      mmio.cpp stack_depth.cpp nondet_static.cpp \
      cfg_dominators.cpp natural_loops.cpp concurrency.cpp \
      dump_c.cpp dot.cpp \
      fence.cpp weak_memory.cpp\
      event_graph.cpp goto2graph.cpp \
      is_threaded.cpp

OBJ += ../ansi-c/ansi-c$(LIBEXT) \
      ../linking/linking$(LIBEXT) \
      ../big-int/bigint$(OBJEXT) \
      ../goto-programs/goto-programs$(LIBEXT) \
      ../goto-symex/goto-symex$(LIBEXT) \
      ../pointer-analysis/pointer-analysis$(LIBEXT) \
      ../langapi/langapi$(LIBEXT) \
      ../util/util$(LIBEXT)

INCLUDES= -I .. -I ../util

LIBS = 

CLEANFILES = goto-instrument$(EXEEXT)

include ../config.inc
include ../common

all: goto-instrument$(EXEEXT)

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

goto-instrument$(EXEEXT): $(OBJ)
	$(LINKBIN)

.PHONY: goto-instrument-mac-signed

goto-instrument-mac-signed: cbmc$(EXEEXT)
	codesign -v -s $(OSX_IDENTITY) goto-instrument$(EXEEXT)

