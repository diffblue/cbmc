SRC = danger/util/danger_program_helper.cpp danger/util/copy_instructions.cpp \
      danger/meta/meta_variable_names.cpp danger/instrument/meta_variables.cpp \
      danger/options/danger_program.cpp \
      danger/constraint/danger_constraint_factory.cpp \
      danger/constant/add_constant.cpp danger/constant/default_constant_strategy.cpp \
      danger/constant/literals_constant_strategy.cpp \
      danger/preprocess/danger_preprocessing.cpp danger/preprocess/remove_loops_and_assertion.cpp \
      danger/preprocess/store_nondet_choices.cpp danger/preprocess/add_invariants_and_temp_variables.cpp \
      danger/symex/learn/danger_library.cpp danger/symex/learn/add_variable_refs.cpp \
      danger/symex/learn/add_counterexamples.cpp danger/symex/learn/add_programs_to_learn.cpp \
      danger/symex/learn/replace_operators.cpp danger/symex/learn/solution_factory.cpp \
      danger/symex/learn/read_x0.cpp danger/symex/learn/instruction_set_factory.cpp \
      danger/symex/learn/danger_learn_config.cpp \
      danger/symex/verify/insert_candidate.cpp danger/symex/verify/insert_constraint.cpp \
      danger/symex/verify/extract_counterexample.cpp danger/symex/verify/restrict_counterexamples.cpp \
      danger/symex/verify/danger_verify_config.cpp

INCLUDES= -I ..

include ../config.inc
include ../common

CLEANFILES = cegis$(LIBEXT)

all: cegis$(LIBEXT)

###############################################################################

cegis$(LIBEXT): $(OBJ)
	$(LINKLIB)

