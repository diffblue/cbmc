SRC = cycles_visitor.cpp \
      fence_assert.cpp \
      fence_inserter.cpp \
      fence_shared.cpp \
      fence_user_def.cpp \
      fencer.cpp \
      graph_visitor.cpp \
      languages.cpp \
      musketeer_main.cpp \
      musketeer_parse_options.cpp \
      pensieve.cpp \
      propagate_const_function_pointers.cpp \
      # Empty last line

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

ifeq ($(BUILD_ENV_),MSVC)
  CP_CXXFLAGS += /DMUSKETEER_VERSION='"""$(CBMC_VERSION) ($(GIT_INFO))"""'
else
  CP_CXXFLAGS += -DMUSKETEER_VERSION="\"$(CBMC_VERSION) ($(GIT_INFO))\""
endif

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
