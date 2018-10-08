SRC = jdiff_languages.cpp \
      jdiff_main.cpp \
      jdiff_parse_options.cpp \
      java_syntactic_diff.cpp \
      # Empty last line

OBJ += ../$(CPROVER_DIR)/src/ansi-c/ansi-c$(LIBEXT) \
      ..//java_bytecode/java_bytecode$(LIBEXT) \
      ../$(CPROVER_DIR)/src/linking/linking$(LIBEXT) \
      ../$(CPROVER_DIR)/src/big-int/big-int$(LIBEXT) \
      ../$(CPROVER_DIR)/src/goto-programs/goto-programs$(LIBEXT) \
      ../$(CPROVER_DIR)/src/pointer-analysis/pointer-analysis$(LIBEXT) \
      ../$(CPROVER_DIR)/src/goto-diff/syntactic_diff$(OBJEXT) \
      ../$(CPROVER_DIR)/src/goto-diff/unified_diff$(OBJEXT) \
      ../$(CPROVER_DIR)/src/goto-diff/change_impact$(OBJEXT) \
      ../$(CPROVER_DIR)/src/goto-diff/goto_diff_base$(OBJEXT) \
      ../$(CPROVER_DIR)/src/goto-instrument/cover$(OBJEXT) \
      ../$(CPROVER_DIR)/src/goto-instrument/cover_basic_blocks$(OBJEXT) \
      ../$(CPROVER_DIR)/src/goto-instrument/cover_filter$(OBJEXT) \
      ../$(CPROVER_DIR)/src/goto-instrument/cover_instrument_branch$(OBJEXT) \
      ../$(CPROVER_DIR)/src/goto-instrument/cover_instrument_condition$(OBJEXT) \
      ../$(CPROVER_DIR)/src/goto-instrument/cover_instrument_decision$(OBJEXT) \
      ../$(CPROVER_DIR)/src/goto-instrument/cover_instrument_location$(OBJEXT) \
      ../$(CPROVER_DIR)/src/goto-instrument/cover_instrument_mcdc$(OBJEXT) \
      ../$(CPROVER_DIR)/src/goto-instrument/cover_instrument_other$(OBJEXT) \
      ../$(CPROVER_DIR)/src/goto-instrument/cover_util$(OBJEXT) \
      ../$(CPROVER_DIR)/src/analyses/analyses$(LIBEXT) \
      ../$(CPROVER_DIR)/src/langapi/langapi$(LIBEXT) \
      ../$(CPROVER_DIR)/src/xmllang/xmllang$(LIBEXT) \
      ../$(CPROVER_DIR)/src/util/util$(LIBEXT) \
      ../miniz/miniz$(OBJEXT) \
      ../$(CPROVER_DIR)/src/json/json$(LIBEXT) \
      # Empty last line

INCLUDES= -I .. -I ../$(CPROVER_DIR)/src

LIBS =

include ../config.inc
include ../$(CPROVER_DIR)/src/config.inc
include ../$(CPROVER_DIR)/src/common

CLEANFILES = jdiff$(EXEEXT)

all: jdiff$(EXEEXT)

###############################################################################

jdiff$(EXEEXT): $(OBJ)
	$(LINKBIN)

.PHONY: jdiff-mac-signed

jdiff-mac-signed: jdiff$(EXEEXT)
	strip jdiff$(EXEEXT) ; codesign -v -s $(OSX_IDENTITY) jdiff$(EXEEXT)
