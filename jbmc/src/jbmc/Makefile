SRC = jbmc_main.cpp \
      jbmc_parse_options.cpp \
      # Empty last line

OBJ += ../$(CPROVER_DIR)/src/ansi-c/ansi-c$(LIBEXT) \
      ../java_bytecode/java_bytecode$(LIBEXT) \
      ../$(CPROVER_DIR)/src/linking/linking$(LIBEXT) \
      ../$(CPROVER_DIR)/src/big-int/big-int$(LIBEXT) \
      ../$(CPROVER_DIR)/src/goto-checker/goto-checker$(LIBEXT) \
      ../$(CPROVER_DIR)/src/goto-programs/goto-programs$(LIBEXT) \
      ../$(CPROVER_DIR)/src/goto-symex/goto-symex$(LIBEXT) \
      ../$(CPROVER_DIR)/src/pointer-analysis/value_set$(OBJEXT) \
      ../$(CPROVER_DIR)/src/pointer-analysis/value_set_analysis_fi$(OBJEXT) \
      ../$(CPROVER_DIR)/src/pointer-analysis/value_set_domain_fi$(OBJEXT) \
      ../$(CPROVER_DIR)/src/pointer-analysis/value_set_fi$(OBJEXT) \
      ../$(CPROVER_DIR)/src/pointer-analysis/value_set_dereference$(OBJEXT) \
      ../$(CPROVER_DIR)/src/pointer-analysis/add_failed_symbols$(OBJEXT) \
      ../$(CPROVER_DIR)/src/pointer-analysis/rewrite_index$(OBJEXT) \
      ../$(CPROVER_DIR)/src/pointer-analysis/goto_program_dereference$(OBJEXT) \
      ../$(CPROVER_DIR)/src/goto-instrument/full_slicer$(OBJEXT) \
      ../$(CPROVER_DIR)/src/goto-instrument/reachability_slicer$(OBJEXT) \
      ../$(CPROVER_DIR)/src/goto-instrument/nondet_static$(OBJEXT) \
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
      ../$(CPROVER_DIR)/src/goto-instrument/unwindset$(OBJEXT) \
      ../$(CPROVER_DIR)/src/analyses/analyses$(LIBEXT) \
      ../$(CPROVER_DIR)/src/langapi/langapi$(LIBEXT) \
      ../$(CPROVER_DIR)/src/xmllang/xmllang$(LIBEXT) \
      ../$(CPROVER_DIR)/src/solvers/solvers$(LIBEXT) \
      ../$(CPROVER_DIR)/src/util/util$(LIBEXT) \
      ../miniz/miniz$(OBJEXT) \
      ../$(CPROVER_DIR)/src/json/json$(LIBEXT) \
      ../$(CPROVER_DIR)/src/cbmc/all_properties$(OBJEXT) \
      ../$(CPROVER_DIR)/src/cbmc/bmc$(OBJEXT) \
      ../$(CPROVER_DIR)/src/cbmc/bmc_cover$(OBJEXT) \
      ../$(CPROVER_DIR)/src/cbmc/counterexample_beautification$(OBJEXT) \
      ../$(CPROVER_DIR)/src/cbmc/fault_localization$(OBJEXT) \
      ../$(CPROVER_DIR)/src/cbmc/symex_bmc$(OBJEXT) \
      ../$(CPROVER_DIR)/src/cbmc/symex_coverage$(OBJEXT) \
      # Empty last line

INCLUDES= -I .. -I ../$(CPROVER_DIR)/src

LIBS =

include ../config.inc
include ../$(CPROVER_DIR)/src/config.inc
include ../$(CPROVER_DIR)/src/common

CLEANFILES = jbmc$(EXEEXT)

all: jbmc$(EXEEXT)

###############################################################################

jbmc$(EXEEXT): $(OBJ)
	$(LINKBIN)

.PHONY: jbmc-mac-signed

jbmc-mac-signed: jbmc$(EXEEXT)
	strip jbmc$(EXEEXT) ; codesign -v -s $(OSX_IDENTITY) jbmc$(EXEEXT)
