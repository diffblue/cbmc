SRC = bmc_util.cpp \
      counterexample_beautification.cpp \
      cover_goals_report_util.cpp \
      incremental_goto_checker.cpp \
      goto_symex_fault_localizer.cpp \
      goto_symex_property_decider.cpp \
      goto_trace_storage.cpp \
      goto_verifier.cpp \
      multi_path_symex_checker.cpp \
      multi_path_symex_only_checker.cpp \
      properties.cpp \
      report_util.cpp \
      single_path_symex_checker.cpp \
      single_path_symex_only_checker.cpp \
      solver_factory.cpp \
      symex_coverage.cpp \
      symex_bmc.cpp \
      # Empty last line

INCLUDES= -I ..

include ../config.inc
include ../common

CLEANFILES = goto-checker$(LIBEXT)

all: goto-checker$(LIBEXT)

###############################################################################

goto-checker$(LIBEXT): $(OBJ)
	$(LINKLIB)
