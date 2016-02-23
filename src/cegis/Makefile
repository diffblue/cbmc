SRC = danger/meta/meta_variable_names.cpp danger/facade/danger_runner.cpp danger/options/danger_program.cpp \
      danger/genetic/dynamic_danger_test_runner.cpp \
      danger/options/danger_program_printer.cpp danger/constraint/danger_constraint_factory.cpp \
      danger/preprocess/danger_preprocessing.cpp danger/preprocess/store_nondet_choices.cpp \
      danger/preprocess/add_ranking_and_skolem_variables.cpp danger/symex/learn/add_variable_refs.cpp \
      danger/symex/learn/add_programs_to_learn.cpp danger/symex/learn/solution_factory.cpp \
      danger/symex/learn/read_x0.cpp danger/symex/learn/add_x0_placeholders.cpp danger/symex/learn/danger_learn_config.cpp \
      danger/symex/learn/encoded_danger_learn_config.cpp danger/symex/verify/insert_candidate.cpp danger/symex/verify/restrict_counterexamples.cpp \
      danger/symex/verify/danger_verify_config.cpp danger/symex/verify/parallel_danger_verifier.cpp \
      danger/symex/verify/parallel_danger_verify_task.cpp danger/symex/fitness/danger_fitness_config.cpp \
      safety/options/safety_program.cpp safety/options/safety_program_printer.cpp safety/preprocessing/safety_preprocessing.cpp \
      safety/genetic/dynamic_safety_test_runner.cpp \
      safety/meta/meta_variable_names.cpp safety/constraint/safety_constraint_factory.cpp \
      safety/symex/learn/safety_learn_config.cpp safety/symex/learn/solution_factory.cpp \
      safety/symex/learn/add_variable_refs.cpp safety/symex/verify/safety_verify_config.cpp \
      safety/symex/learn/encoded_safety_learn_config.cpp safety/symex/learn/add_counterexamples.cpp \
      safety/symex/verify/insert_candidate.cpp safety/facade/safety_runner.cpp \
      safety/symex/fitness/safety_fitness_config.cpp safety/value/safety_goto_ce.cpp \
      safety/value/individual_to_safety_solution_deserialiser.cpp \
      invariant/options/invariant_program.cpp invariant/options/target_copy_helper.cpp \
      invariant/util/copy_instructions.cpp invariant/util/invariant_program_helper.cpp \
      invariant/util/invariant_constraint_variables.cpp invariant/instrument/meta_variables.cpp \
      invariant/constant/add_constant.cpp invariant/constant/default_constant_strategy.cpp \
      invariant/constant/literals_constant_strategy.cpp invariant/meta/meta_variable_names.cpp \
      invariant/preprocess/add_invariants_and_temp_variables.cpp invariant/preprocess/remove_loops_and_assertion.cpp \
      invariant/symex/learn/add_counterexamples.cpp invariant/symex/learn/add_invariant_programs_to_learn.cpp \
      invariant/symex/learn/instrument_vars.cpp invariant/symex/learn/invariant_library.cpp \
      invariant/symex/learn/replace_operators.cpp invariant/symex/verify/extract_counterexample.cpp \
      invariant/symex/verify/insert_constraint.cpp invariant/symex/verify/insert_program.cpp \
      invariant/fitness/concrete_fitness_source_provider.cpp \
      wordsize/restrict_bv_size.cpp value/program_individual_serialisation.cpp \
      seed/literals_seed.cpp genetic/tournament_select.cpp genetic/match_select.cpp \
      genetic/instruction_set_info_factory.cpp genetic/random_mutate.cpp genetic/random_cross.cpp \
      genetic/random_individual.cpp genetic/genetic_constant_strategy.cpp instructions/instruction_set_factory.cpp \
      genetic/concrete_test_runner.cpp genetic/dynamic_test_runner_helper.cpp genetic/genetic_settings.cpp \
      cegis-util/task_pool.cpp cegis-util/constant_width.cpp cegis-util/irep_pipe.cpp \
      runner/cegis_parse_options.cpp runner/cegis_main.cpp \
      ../goto-instrument/dump_c.cpp ../goto-instrument/goto_program2code.cpp \
      ../cbmc/cbmc_parse_options.cpp ../cbmc/bmc.cpp ../cbmc/cbmc_solvers.cpp ../cbmc/symex_bmc.cpp \
      ../cbmc/xml_interface.cpp ../cbmc/cover.cpp ../cbmc/bv_cbmc.cpp ../cbmc/counterexample_beautification.cpp \
      ../cbmc/cbmc_languages.cpp ../cbmc/show_vcc.cpp ../cbmc/cbmc_dimacs.cpp ../cbmc/all_properties.cpp

OBJ += ../ansi-c/ansi-c$(LIBEXT) \
      ../cpp/cpp$(LIBEXT) \
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
      ../analyses/analyses$(LIBEXT) \
      ../langapi/langapi$(LIBEXT) \
      ../xmllang/xmllang$(LIBEXT) \
      ../assembler/assembler$(LIBEXT) \
      ../solvers/solvers$(LIBEXT) \
      ../util/util$(LIBEXT)

INCLUDES= -I ..

LIBS = $(DLFCN_LINKFLAGS)

include ../config.inc
include ../common

CLEANFILES = cegis$(EXEEXT)

all: cegis$(EXEEXT)

###############################################################################

cegis$(EXEEXT): $(OBJ)
	$(LINKBIN)

