SRC = \
  api.cpp \
  api_options.cpp \
  verification_result.cpp \
  # Empty last line

OBJ += \
  ../analyses/analyses$(LIBEXT) \
  ../ansi-c/ansi-c$(LIBEXT) \
  ../assembler/assembler$(LIBEXT) \
  ../big-int/big-int$(LIBEXT) \
  ../goto-checker/goto-checker$(LIBEXT) \
  ../goto-instrument/cover$(OBJEXT) \
  ../goto-instrument/cover_basic_blocks$(OBJEXT) \
  ../goto-instrument/cover_filter$(OBJEXT) \
  ../goto-instrument/cover_instrument_assume$(OBJEXT) \
  ../goto-instrument/cover_instrument_branch$(OBJEXT) \
  ../goto-instrument/cover_instrument_condition$(OBJEXT) \
  ../goto-instrument/cover_instrument_decision$(OBJEXT) \
  ../goto-instrument/cover_instrument_location$(OBJEXT) \
  ../goto-instrument/cover_instrument_mcdc$(OBJEXT) \
  ../goto-instrument/cover_instrument_other$(OBJEXT) \
  ../goto-instrument/cover_util$(OBJEXT) \
  ../goto-instrument/full_slicer$(OBJEXT) \
  ../goto-instrument/nondet_static$(OBJEXT) \
  ../goto-instrument/reachability_slicer$(OBJEXT) \
  ../goto-instrument/source_lines$(OBJEXT) \
  ../goto-instrument/unwindset$(OBJEXT) \
  ../goto-programs/goto-programs$(LIBEXT) \
  ../goto-symex/goto-symex$(LIBEXT) \
  ../json-symtab-language/json-symtab-language$(LIBEXT) \
  ../json/json$(LIBEXT) \
  ../langapi/langapi$(LIBEXT) \
  ../linking/linking$(LIBEXT) \
  ../pointer-analysis/add_failed_symbols$(OBJEXT) \
  ../pointer-analysis/goto_program_dereference$(OBJEXT) \
  ../pointer-analysis/value_set$(OBJEXT) \
  ../pointer-analysis/value_set_analysis_fi$(OBJEXT) \
  ../pointer-analysis/value_set_dereference$(OBJEXT) \
  ../pointer-analysis/value_set_domain_fi$(OBJEXT) \
  ../pointer-analysis/value_set_fi$(OBJEXT) \
  ../solvers/solvers$(LIBEXT) \
  ../statement-list/statement-list$(LIBEXT) \
  ../util/util$(LIBEXT) \
  ../xmllang/xmllang$(LIBEXT) \
  # Empty last line

INCLUDES = -I ..

include ../config.inc
include ../common

CLEANFILES = libcprover-cpp$(LIBEXT)

all: libcprover-cpp$(LIBEXT)

###############################################################################

libcprover-cpp$(LIBEXT): $(OBJ)
	$(LINKLIB)
