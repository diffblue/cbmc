SRC = value_set.cpp goto_program_dereference.cpp value_set_analysis.cpp \
      dereference.cpp pointer_offset_sum.cpp add_failed_symbols.cpp \
      show_value_sets.cpp value_set_domain.cpp rewrite_index.cpp \
      value_set_analysis_fi.cpp value_set_fi.cpp value_set_domain_fi.cpp \
      value_set_analysis_fivr.cpp value_set_fivr.cpp value_set_domain_fivr.cpp \
      value_set_analysis_fivrns.cpp value_set_fivrns.cpp \
      value_set_domain_fivrns.cpp

INCLUDES= -I .. -I ../util

include ../config.inc
include ../common

CLEANFILES = pointer-analysis$(LIBEXT)

all: pointer-analysis$(LIBEXT)

###############################################################################

pointer-analysis$(LIBEXT): $(OBJ)
	$(LINKLIB)

