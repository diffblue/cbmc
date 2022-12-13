SRC = enumerative_loop_contracts_synthesizer.cpp \
      expr_enumerator.cpp \
      goto_synthesizer_languages.cpp \
      goto_synthesizer_main.cpp \
      goto_synthesizer_parse_options.cpp \
      synthesizer_utils.cpp \
      # Empty last line

OBJ += ../ansi-c/ansi-c$(LIBEXT) \
      ../analyses/analyses$(LIBEXT) \
      ../cpp/cpp$(LIBEXT) \
      ../linking/linking$(LIBEXT) \
      ../big-int/big-int$(LIBEXT) \
      ../goto-checker/goto-checker$(LIBEXT) \
      ../goto-programs/goto-programs$(LIBEXT) \
      ../goto-instrument/contracts/contracts$(OBJEXT) \
      ../goto-instrument/contracts/utils$(OBJEXT) \
      ../goto-instrument/contracts/instrument_spec_assigns$(OBJEXT) \
      ../goto-instrument/contracts/memory_predicates$(OBJEXT) \
      ../goto-instrument/contracts/inlining_decorator$(OBJEXT) \
      ../goto-instrument/contracts/havoc_assigns_clause_targets$(OBJEXT) \
      ../goto-instrument/havoc_utils$(OBJEXT) \
      ../goto-instrument/loop_utils$(OBJEXT) \
      ../goto-instrument/unwindset$(OBJEXT) \
      ../goto-instrument/unwind$(OBJEXT) \
      ../goto-instrument/nondet_static$(OBJEXT) \
      ../langapi/langapi$(LIBEXT) \
      ../util/util$(LIBEXT) \
      ../json/json$(LIBEXT) \
      # Empty last line

INCLUDES= -I ..

LIBS =

CLEANFILES = goto-synthesizer$(EXEEXT) goto-synthesizer$(LIBEXT)

include ../config.inc
include ../common

all: goto-synthesizer$(EXEEXT)

###############################################################################

goto-synthesizer$(EXEEXT): $(OBJ)
	$(LINKBIN)

.PHONY: goto-synthesizer-mac-signed

goto-synthesizer-mac-signed: goto-synthesizer$(EXEEXT)
	codesign -v -s $(OSX_IDENTITY) goto-synthesizer$(EXEEXT)
