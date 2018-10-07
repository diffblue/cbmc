SRC = change_impact.cpp \
      goto_diff_base.cpp \
      goto_diff_languages.cpp \
      goto_diff_main.cpp \
      goto_diff_parse_options.cpp \
      syntactic_diff.cpp \
      unified_diff.cpp \
      # Empty last line

OBJ += ../ansi-c/ansi-c$(LIBEXT) \
      ../cpp/cpp$(LIBEXT) \
      ../linking/linking$(LIBEXT) \
      ../big-int/big-int$(LIBEXT) \
      ../goto-programs/goto-programs$(LIBEXT) \
      ../assembler/assembler$(LIBEXT) \
      ../pointer-analysis/pointer-analysis$(LIBEXT) \
      ../goto-instrument/cover$(OBJEXT) \
      ../goto-instrument/cover_basic_blocks$(OBJEXT) \
      ../goto-instrument/cover_filter$(OBJEXT) \
      ../goto-instrument/cover_instrument_branch$(OBJEXT) \
      ../goto-instrument/cover_instrument_condition$(OBJEXT) \
      ../goto-instrument/cover_instrument_decision$(OBJEXT) \
      ../goto-instrument/cover_instrument_location$(OBJEXT) \
      ../goto-instrument/cover_instrument_mcdc$(OBJEXT) \
      ../goto-instrument/cover_instrument_other$(OBJEXT) \
      ../goto-instrument/cover_util$(OBJEXT) \
      ../analyses/analyses$(LIBEXT) \
      ../langapi/langapi$(LIBEXT) \
      ../xmllang/xmllang$(LIBEXT) \
      ../util/util$(LIBEXT) \
      ../solvers/solvers$(LIBEXT) \
      ../json/json$(LIBEXT) \
      # Empty last line

INCLUDES= -I ..

LIBS =

include ../config.inc
include ../common

CLEANFILES = goto-diff$(EXEEXT)

all: goto-diff$(EXEEXT)

###############################################################################

goto-diff$(EXEEXT): $(OBJ)
	$(LINKBIN)

.PHONY: goto-diff-mac-signed

goto-diff-mac-signed: goto-diff$(EXEEXT)
	strip goto-diff$(EXEEXT) ; codesign -v -s $(OSX_IDENTITY) goto-diff$(EXEEXT)
