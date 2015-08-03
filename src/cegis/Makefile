SRC = bmc/bmc_verification_oracle.cpp symex/symex_learn.cpp \
      symex/variables_factory.cpp symex/candidate_factory.cpp \
      symex/symex_learning_program_adapter.cpp symex/cegis_library.cpp \
      symex/target_program_factory.cpp symex/test_case_factory.cpp \
      util/goto_program_adapter.cpp util/source_location_factory.cpp \
      options/cegis_options.cpp

INCLUDES= -I ..

include ../config.inc
include ../common

CLEANFILES = cegis$(LIBEXT)

all: cegis$(LIBEXT)

###############################################################################

cegis$(LIBEXT): $(OBJ)
	$(LINKLIB)

