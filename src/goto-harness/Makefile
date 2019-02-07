SRC = \
  function_call_harness_generator.cpp \
  goto_harness_generator.cpp \
  goto_harness_generator_factory.cpp \
  goto_harness_main.cpp \
  goto_harness_parse_options.cpp \
  memory_snapshot_harness_generator.cpp \
  recursive_initialization.cpp \
  # Empty last line

OBJ += \
  ../util/util$(LIBEXT) \
  ../goto-programs/goto-programs$(LIBEXT) \
  ../big-int/big-int$(LIBEXT) \
  ../langapi/langapi$(LIBEXT) \
  ../linking/linking$(LIBEXT) \
  ../json/json$(LIBEXT) \
  ../json-symtab-language/json-symtab-language$(LIBEXT) \
  # Empty last line

INCLUDES= -I ..

LIBS =

CLEANFILES = goto-harness$(EXEEXT)

include ../config.inc
include ../common

all: goto-harness$(EXEEXT)

###############################################################################

goto-harness$(EXEEXT): $(OBJ)
	$(LINKBIN)

.PHONY: goto-harness-mac-signed

goto-harness-mac-signed: goto-harness$(EXEEXT)
	codesign -v -s $(OSX_IDENTITY) goto-harness$(EXEEXT)
