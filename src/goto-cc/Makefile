SRC = armcc_cmdline.cpp \
      armcc_mode.cpp \
      as86_cmdline.cpp \
      as_cmdline.cpp \
      as_mode.cpp \
      bcc_cmdline.cpp \
      compile.cpp \
      cw_mode.cpp \
      gcc_cmdline.cpp \
      gcc_mode.cpp \
      goto_cc_cmdline.cpp \
      goto_cc_languages.cpp \
      goto_cc_main.cpp \
      goto_cc_mode.cpp \
      ld_cmdline.cpp \
      ms_cl_cmdline.cpp \
      ms_cl_mode.cpp \
      # Empty last line

OBJ += ../big-int/big-int$(LIBEXT) \
      ../goto-programs/goto-programs$(LIBEXT) \
      ../util/util$(LIBEXT) \
      ../linking/linking$(LIBEXT) \
      ../ansi-c/ansi-c$(LIBEXT) \
      ../cpp/cpp$(LIBEXT) \
      ../xmllang/xmllang$(LIBEXT) \
      ../assembler/assembler$(LIBEXT) \
      ../langapi/langapi$(LIBEXT) \
      ../miniz/miniz$(OBJEXT) \
      ../json/json$(LIBEXT)

INCLUDES= -I ..

LIBS =

CLEANFILES = goto-cc$(EXEEXT) goto-cl$(EXEEXT)

include ../config.inc
include ../common

ifeq ($(BUILD_ENV_),MSVC)
all: goto-cl$(EXEEXT)
endif
all: goto-cc$(EXEEXT)

CP_CXXFLAGS += -DCBMC_VERSION="\"$(CBMC_VERSION) ($(GIT_INFO))\""

ifneq ($(wildcard ../java_bytecode/Makefile),)
  OBJ += ../java_bytecode/java_bytecode$(LIBEXT)
endif

ifneq ($(wildcard ../jsil/Makefile),)
  OBJ += ../jsil/jsil$(LIBEXT)
  CP_CXXFLAGS += -DHAVE_JSIL
endif

###############################################################################

goto-cc$(EXEEXT): $(OBJ)
	$(LINKBIN)

goto-cl$(EXEEXT): $(OBJ)
	$(LINKBIN)

.PHONY: goto-cc-mac-signed

goto-cc-mac-signed: goto-cc$(EXEEXT)
	codesign -v -s $(OSX_IDENTITY) goto-cc$(EXEEXT)
