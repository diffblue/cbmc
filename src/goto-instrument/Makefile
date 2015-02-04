SRC = goto_instrument_parse_options.cpp rw_set.cpp \
      document_properties.cpp goto_instrument_languages.cpp \
      uninitialized.cpp full_slicer.cpp k_induction.cpp \
      object_id.cpp show_locations.cpp points_to.cpp \
      alignment_checks.cpp race_check.cpp \
      nondet_volatile.cpp interrupt.cpp function.cpp branch.cpp \
      mmio.cpp stack_depth.cpp nondet_static.cpp \
      concurrency.cpp dump_c.cpp dot.cpp havoc_loops.cpp \
      call_sequences.cpp unwind.cpp function_modifies.cpp \
      accelerate/accelerate.cpp accelerate/polynomial.cpp \
      accelerate/scratch_program.cpp accelerate/polynomial_accelerator.cpp \
      accelerate/util.cpp accelerate/trace_automaton.cpp \
      accelerate/enumerating_loop_acceleration.cpp \
      accelerate/all_paths_enumerator.cpp \
      accelerate/sat_path_enumerator.cpp \
      accelerate/disjunctive_polynomial_acceleration.cpp \
      accelerate/cone_of_influence.cpp accelerate/overflow_instrumenter.cpp\
      accelerate/path.cpp accelerate/acceleration_utils.cpp \
      count_eloc.cpp reachability_slicer.cpp goto_program2code.cpp \
      wmm/abstract_event.cpp wmm/fence.cpp wmm/shared_buffers.cpp \
      wmm/cycle_collection.cpp wmm/goto2graph.cpp wmm/weak_memory.cpp \
      wmm/data_dp.cpp wmm/instrumenter_strategies.cpp \
      wmm/event_graph.cpp wmm/pair_collection.cpp \
      goto_instrument_main.cpp

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
      ../solvers/solvers$(LIBEXT)

INCLUDES= -I ..

LIBS = 

CLEANFILES = goto-instrument$(EXEEXT)

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

