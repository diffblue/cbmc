SRC = languages.cpp fencer.cpp fence_inserter.cpp musketeer_main.cpp \
      musketeer_parseoptions.cpp fence_assert.cpp fence_user_def.cpp \
      fence_shared.cpp pensieve.cpp propagate_const_function_pointers.cpp \
      graph_visitor.cpp cycles_visitor.cpp

OBJ += ../goto-instrument/wmm-cycles$(LIBEXT)

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

