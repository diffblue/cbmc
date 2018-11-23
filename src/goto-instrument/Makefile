SRC = accelerate/accelerate.cpp \
      accelerate/acceleration_utils.cpp \
      accelerate/all_paths_enumerator.cpp \
      accelerate/cone_of_influence.cpp \
      accelerate/disjunctive_polynomial_acceleration.cpp \
      accelerate/enumerating_loop_acceleration.cpp \
      accelerate/overflow_instrumenter.cpp \
      accelerate/path.cpp \
      accelerate/polynomial.cpp \
      accelerate/polynomial_accelerator.cpp \
      accelerate/sat_path_enumerator.cpp \
      accelerate/scratch_program.cpp \
      accelerate/trace_automaton.cpp \
      accelerate/util.cpp \
      aggressive_slicer.cpp \
      alignment_checks.cpp \
      branch.cpp \
      call_sequences.cpp \
      code_contracts.cpp \
      concurrency.cpp \
      count_eloc.cpp \
      cover.cpp \
      cover_basic_blocks.cpp \
      cover_filter.cpp \
      cover_instrument_branch.cpp \
      cover_instrument_condition.cpp \
      cover_instrument_decision.cpp \
      cover_instrument_location.cpp \
      cover_instrument_mcdc.cpp \
      cover_instrument_other.cpp \
      cover_util.cpp \
      document_properties.cpp \
      dot.cpp \
      dump_c.cpp \
      full_slicer.cpp \
      function.cpp \
      function_modifies.cpp \
      generate_function_bodies.cpp \
      goto_instrument_languages.cpp \
      goto_instrument_main.cpp \
      goto_instrument_parse_options.cpp \
      goto_program2code.cpp \
      havoc_loops.cpp \
      horn_encoding.cpp \
      interrupt.cpp \
      k_induction.cpp \
      loop_utils.cpp \
      mmio.cpp \
      model_argc_argv.cpp \
      nondet_static.cpp \
      nondet_volatile.cpp \
      object_id.cpp \
      points_to.cpp \
      race_check.cpp \
      reachability_slicer.cpp \
      remove_function.cpp \
      rw_set.cpp \
      show_locations.cpp \
      skip_loops.cpp \
      splice_call.cpp \
      stack_depth.cpp \
      thread_instrumentation.cpp \
      undefined_functions.cpp \
      uninitialized.cpp \
      unwind.cpp \
      unwindset.cpp \
      wmm/abstract_event.cpp \
      wmm/cycle_collection.cpp \
      wmm/data_dp.cpp \
      wmm/event_graph.cpp \
      wmm/fence.cpp \
      wmm/goto2graph.cpp \
      wmm/instrumenter_strategies.cpp \
      wmm/pair_collection.cpp \
      wmm/shared_buffers.cpp \
      wmm/weak_memory.cpp \
      # Empty last line

OBJ += ../ansi-c/ansi-c$(LIBEXT) \
      ../cpp/cpp$(LIBEXT) \
      ../linking/linking$(LIBEXT) \
      ../big-int/big-int$(LIBEXT) \
      ../goto-programs/goto-programs$(LIBEXT) \
      ../goto-symex/goto-symex$(LIBEXT) \
      ../assembler/assembler$(LIBEXT) \
      ../pointer-analysis/pointer-analysis$(LIBEXT) \
      ../analyses/analyses$(LIBEXT) \
      ../langapi/langapi$(LIBEXT) \
      ../xmllang/xmllang$(LIBEXT) \
      ../util/util$(LIBEXT) \
      ../solvers/solvers$(LIBEXT) \
      ../json/json$(LIBEXT) \
      # Empty last line

INCLUDES= -I ..

LIBS =

CLEANFILES = goto-instrument$(EXEEXT) goto-instrument$(LIBEXT)

include ../config.inc
include ../common

all: goto-instrument$(EXEEXT)

ifneq ($(LIB_GLPK),)
  LIBS += $(LIB_GLPK)
  CP_CXXFLAGS += -DHAVE_GLPK
endif

###############################################################################

goto-instrument$(EXEEXT): $(OBJ)
	$(LINKBIN)

.PHONY: goto-instrument-mac-signed

goto-instrument-mac-signed: goto-instrument$(EXEEXT)
	codesign -v -s $(OSX_IDENTITY) goto-instrument$(EXEEXT)
