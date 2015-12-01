SRC = danger/util/danger_program_helper.cpp danger/util/copy_instructions.cpp \
      danger/meta/meta_variable_names.cpp danger/instrument/meta_variables.cpp \
      danger/facade/danger_runner.cpp danger/options/danger_program.cpp \
      danger/options/danger_program_printer.cpp danger/constraint/danger_constraint_factory.cpp \
      danger/constant/add_constant.cpp danger/constant/default_constant_strategy.cpp \
      danger/constant/literals_constant_strategy.cpp \
      danger/fitness/concrete_fitness_source_provider.cpp \
      danger/preprocess/danger_preprocessing.cpp danger/preprocess/remove_loops_and_assertion.cpp \
      danger/preprocess/store_nondet_choices.cpp danger/preprocess/add_invariants_and_temp_variables.cpp \
      danger/symex/learn/danger_library.cpp danger/symex/learn/add_variable_refs.cpp \
      danger/symex/learn/add_counterexamples.cpp danger/symex/learn/add_programs_to_learn.cpp \
      danger/symex/learn/replace_operators.cpp danger/symex/learn/solution_factory.cpp \
      danger/symex/learn/read_x0.cpp danger/symex/learn/add_x0_placeholders.cpp \
      danger/symex/learn/danger_learn_config.cpp danger/symex/learn/danger_body_provider.cpp \
      danger/symex/learn/encoded_danger_learn_config.cpp \
      danger/symex/verify/insert_candidate.cpp danger/symex/verify/insert_constraint.cpp \
      danger/symex/verify/extract_counterexample.cpp danger/symex/verify/restrict_counterexamples.cpp \
      danger/symex/verify/danger_verify_config.cpp danger/symex/verify/parallel_danger_verifier.cpp \
      danger/symex/verify/parallel_danger_verify_task.cpp danger/symex/fitness/danger_fitness_config.cpp \
      wordsize/restrict_bv_size.cpp value/program_individual_serialisation.cpp \
      seed/null_seed.cpp seed/literals_seed.cpp genetic/tournament_select.cpp genetic/match_select.cpp \
      genetic/instruction_set_info_factory.cpp genetic/random_mutate.cpp genetic/random_cross.cpp \
      genetic/random_individual.cpp genetic/genetic_constant_strategy.cpp instructions/instruction_set_factory.cpp \
      genetic/concrete_test_runner.cpp genetic/dynamic_test_runner.cpp \
      ../goto-instrument/dump_c.cpp ../goto-instrument/goto_program2code.cpp

INCLUDES= -I ..

include ../config.inc
include ../common

CLEANFILES = cegis$(LIBEXT)

all: cegis$(LIBEXT)

###############################################################################

cegis$(LIBEXT): $(OBJ)
	$(LINKLIB)

