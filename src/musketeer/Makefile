SRC = languages.cpp fencer.cpp fence_inserter.cpp musketeer_main.cpp \
      musketeer_parseoptions.cpp fence_assert.cpp fence_user_def.cpp \
      fence_shared.cpp pensieve.cpp propagate_const_function_pointers.cpp \
      graph_visitor.cpp cycles_visitor.cpp

OBJ += ../ansi-c/ansi-c$(LIBEXT) \
      ../linking/linking$(LIBEXT) \
      ../big-int/big-int$(LIBEXT) \
      ../goto-programs/goto-programs$(LIBEXT) \
      ../goto-symex/goto-symex$(LIBEXT) \
      ../assembler/assembler$(LIBEXT) \
      ../pointer-analysis/pointer-analysis$(LIBEXT) \
      ../analyses/analyses$(LIBEXT) \
      ../langapi/langapi$(LIBEXT) \
      ../util/util$(LIBEXT) \
      ../solvers/solvers$(LIBEXT) \
      ../goto-instrument/wmm/weak_memory$(OBJEXT) \
      ../goto-instrument/wmm/fence$(OBJEXT) \
      ../goto-instrument/wmm/event_graph$(OBJEXT) \
      ../goto-instrument/wmm/goto2graph$(OBJEXT) \
      ../goto-instrument/wmm/data_dp$(OBJEXT) \
      ../goto-instrument/wmm/abstract_event$(OBJEXT) \
      ../goto-instrument/wmm/instrumenter_strategies$(OBJEXT) \
      ../goto-instrument/wmm/cycle_collection$(OBJEXT) \
      ../goto-instrument/wmm/shared_buffers$(OBJEXT) \
      ../goto-instrument/wmm/pair_collection$(OBJEXT) \
      ../goto-instrument/rw_set$(OBJEXT)

INCLUDES= -I ..

LIBS =

CLEANFILES = musketeer$(EXEEXT)

include ../config.inc
include ../common

all: musketeer$(EXEEXT)

ifneq ($(LIB_GLPK),)
  LIBS += $(LIB_GLPK)
  CP_CXXFLAGS += -DHAVE_GLPK
endif

###############################################################################

musketeer$(EXEEXT): $(OBJ)
	$(LINKBIN)

.PHONY: musketeer-mac-signed

musketeer-mac-signed: musketeer$(EXEEXT)
	codesign -v -s $(OSX_IDENTITY) musketeer$(EXEEXT)

