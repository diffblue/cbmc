SRC = jbmc_main.cpp \
      jbmc_parse_options.cpp \
      # Empty last line

OBJ += ../ansi-c/ansi-c$(LIBEXT) \
      ../java_bytecode/java_bytecode$(LIBEXT) \
      ../linking/linking$(LIBEXT) \
      ../big-int/big-int$(LIBEXT) \
      ../goto-programs/goto-programs$(LIBEXT) \
      ../goto-symex/goto-symex$(LIBEXT) \
      ../pointer-analysis/value_set$(OBJEXT) \
      ../pointer-analysis/value_set_analysis_fi$(OBJEXT) \
      ../pointer-analysis/value_set_domain_fi$(OBJEXT) \
      ../pointer-analysis/value_set_fi$(OBJEXT) \
      ../pointer-analysis/value_set_dereference$(OBJEXT) \
      ../pointer-analysis/dereference_callback$(OBJEXT) \
      ../pointer-analysis/add_failed_symbols$(OBJEXT) \
      ../pointer-analysis/rewrite_index$(OBJEXT) \
      ../pointer-analysis/goto_program_dereference$(OBJEXT) \
      ../goto-instrument/full_slicer$(OBJEXT) \
      ../goto-instrument/nondet_static$(OBJEXT) \
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
      ../assembler/assembler$(LIBEXT) \
      ../solvers/solvers$(LIBEXT) \
      ../util/util$(LIBEXT) \
      ../miniz/miniz$(OBJEXT) \
      ../json/json$(LIBEXT) \
      ../cbmc/all_properties$(OBJEXT) \
      ../cbmc/bmc$(OBJEXT) \
      ../cbmc/bmc_cover$(OBJEXT) \
      ../cbmc/bv_cbmc$(OBJEXT) \
      ../cbmc/cbmc_dimacs$(OBJEXT) \
      ../cbmc/cbmc_solvers$(OBJEXT) \
      ../cbmc/counterexample_beautification$(OBJEXT) \
      ../cbmc/fault_localization$(OBJEXT) \
      ../cbmc/show_vcc$(OBJEXT) \
      ../cbmc/symex_bmc$(OBJEXT) \
      ../cbmc/symex_coverage$(OBJEXT) \
      # Empty last line

INCLUDES= -I ..

LIBS =

include ../config.inc
include ../common

CLEANFILES = jbmc$(EXEEXT)

all: jbmc$(EXEEXT)

###############################################################################

jbmc$(EXEEXT): $(OBJ)
	$(LINKBIN)

.PHONY: jbmc-mac-signed

jbmc-mac-signed: jbmc$(EXEEXT)
	strip jbmc$(EXEEXT) ; codesign -v -s $(OSX_IDENTITY) jbmc$(EXEEXT)
