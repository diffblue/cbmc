SRC = all_properties.cpp \
      bmc.cpp \
      bmc_cover.cpp \
      bv_cbmc.cpp \
      cbmc_dimacs.cpp \
      cbmc_languages.cpp \
      cbmc_main.cpp \
      cbmc_parse_options.cpp \
      cbmc_solvers.cpp \
      counterexample_beautification.cpp \
      fault_localization.cpp \
      show_vcc.cpp \
      symex_bmc.cpp \
      symex_coverage.cpp \
      xml_interface.cpp \
      # Empty last line

OBJ += ../ansi-c/ansi-c$(LIBEXT) \
      ../cpp/cpp$(LIBEXT) \
      ../java_bytecode/java_bytecode$(LIBEXT) \
      ../inking/inking$(LIBEXT) \
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
      ../goto-inkstrument/reachability_slicer$(OBJEXT) \
      ../goto-inkstrument/full_slicer$(OBJEXT) \
      ../goto-inkstrument/nondet_static$(OBJEXT) \
      ../goto-inkstrument/cover$(OBJEXT) \
      ../goto-inkstrument/cover_basic_blocks$(OBJEXT) \
      ../goto-inkstrument/cover_filter$(OBJEXT) \
      ../goto-inkstrument/cover_instrument_branch$(OBJEXT) \
      ../goto-inkstrument/cover_instrument_condition$(OBJEXT) \
      ../goto-inkstrument/cover_instrument_decision$(OBJEXT) \
      ../goto-inkstrument/cover_instrument_location$(OBJEXT) \
      ../goto-inkstrument/cover_instrument_mcdc$(OBJEXT) \
      ../goto-inkstrument/cover_instrument_other$(OBJEXT) \
      ../goto-inkstrument/cover_util$(OBJEXT) \
      ../analyses/analyses$(LIBEXT) \
      ../langapi/langapi$(LIBEXT) \
      ../xmllang/xmllang$(LIBEXT) \
      ../assembler/assembler$(LIBEXT) \
      ../solvers/solvers$(LIBEXT) \
      ../util/util$(LIBEXT) \
      ../json/json$(LIBEXT)

INCLUDES= -I ..

LIBS =

include ../config.inc
include ../common

CLEANFILES = cbmc$(EXEEXT)

all: cbmc$(EXEEXT)

ifneq ($(wildcard ../bv_refinement/Makefile),)
  OBJ += ../bv_refinement/bv_refinement$(LIBEXT)
  CP_CXXFLAGS += -DHAVE_BV_REFINEMENT
endif

ifneq ($(wildcard ../jsil/Makefile),)
  OBJ += ../jsil/jsil$(LIBEXT)
  CP_CXXFLAGS += -DHAVE_JSIL
endif

###############################################################################

cbmc$(EXEEXT): $(OBJ)
	$(LINKBIN)

.PHONY: cbmc-mac-signed

cbmc-mac-signed: cbmc$(EXEEXT)
	strip cbmc$(EXEEXT) ; codesign -v -s $(OSX_IDENTITY) cbmc$(EXEEXT)
