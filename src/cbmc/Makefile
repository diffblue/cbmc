SRC = all_properties.cpp \
      bmc.cpp \
      bmc_cover.cpp \
      bmc_util.cpp \
      cbmc_languages.cpp \
      cbmc_main.cpp \
      cbmc_parse_options.cpp \
      counterexample_beautification.cpp \
      fault_localization.cpp \
      symex_bmc.cpp \
      symex_coverage.cpp \
      xml_interface.cpp \
      # Empty last line

OBJ += ../ansi-c/ansi-c$(LIBEXT) \
      ../cpp/cpp$(LIBEXT) \
      ../json/json$(LIBEXT) \
      ../json-symtab-language/json-symtab-language$(LIBEXT) \
      ../linking/linking$(LIBEXT) \
      ../big-int/big-int$(LIBEXT) \
      ../goto-checker/goto-checker$(LIBEXT) \
      ../goto-programs/goto-programs$(LIBEXT) \
      ../goto-symex/goto-symex$(LIBEXT) \
      ../pointer-analysis/value_set$(OBJEXT) \
      ../pointer-analysis/value_set_analysis_fi$(OBJEXT) \
      ../pointer-analysis/value_set_domain_fi$(OBJEXT) \
      ../pointer-analysis/value_set_fi$(OBJEXT) \
      ../pointer-analysis/value_set_dereference$(OBJEXT) \
      ../pointer-analysis/add_failed_symbols$(OBJEXT) \
      ../pointer-analysis/rewrite_index$(OBJEXT) \
      ../pointer-analysis/goto_program_dereference$(OBJEXT) \
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
      ../goto-instrument/reachability_slicer$(OBJEXT) \
      ../goto-instrument/nondet_static$(OBJEXT) \
      ../goto-instrument/full_slicer$(OBJEXT) \
      ../goto-instrument/unwindset$(OBJEXT) \
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
