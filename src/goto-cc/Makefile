SRC = goto-cc.cpp goto_cc_mode.cpp gcc_mode.cpp \
      get_base_name.cpp \
      gcc_cmdline.cpp ms_cl_cmdline.cpp \
      compile.cpp armcc_cmdline.cpp run.cpp \
      languages.cpp goto_cc_cmdline.cpp \
      ms_cl_mode.cpp armcc_mode.cpp cw_mode.cpp

OBJ += ../big-int/bigint$(OBJEXT) \
      ../goto-programs/goto-programs$(LIBEXT) \
      ../pointer-analysis/pointer-analysis$(LIBEXT) \
      ../util/util$(LIBEXT) \
      ../linking/linking$(LIBEXT) \
      ../ansi-c/ansi-c$(LIBEXT) \
      ../xmllang/xmllang$(LIBEXT) \
      ../assembler/assembler$(LIBEXT) \
      ../langapi/langapi$(LIBEXT)

INCLUDES= -I .. -I ../util

LIBS =

CLEANFILES = goto-cc$(EXEEXT)

include ../config.inc
include ../common

all: goto-cc$(EXEEXT)

ifneq ($(wildcard ../cpp/Makefile),)
  OBJ += ../cpp/cpp$(LIBEXT)
  CP_CXXFLAGS += -D HAVE_CPP
endif

###############################################################################

goto-cc$(EXEEXT): $(OBJ)
	$(LINKBIN)

.PHONY: goto-cc-mac-signed

goto-cc-mac-signed: goto-cc$(EXEEXT)
	codesign -v -s $(OSX_IDENTITY) goto-cc$(EXEEXT)

