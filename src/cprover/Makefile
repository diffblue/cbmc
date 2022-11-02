SRC = address_taken.cpp \
      axioms.cpp \
      bv_pointers_wide.cpp \
      c_safety_checks.cpp \
      cprover_main.cpp \
      cprover_parse_options.cpp \
      constant_propagation.cpp \
      counterexample_found.cpp \
      endianness_map_wide.cpp \
      equality_propagation.cpp \
      find_variables.cpp \
      flatten_ok_expr.cpp \
      format_hooks.cpp \
      free_symbols.cpp \
      generalization.cpp \
      inductiveness.cpp \
      instrument_contracts.cpp \
      instrument_given_invariants.cpp \
      may_alias.cpp \
      may_be_same_object.cpp \
      propagate.cpp \
      report_properties.cpp \
      report_traces.cpp \
      sentinel_dll.cpp \
      simplify_state_expr.cpp \
      state.cpp \
      state_encoding.cpp \
      state_encoding_targets.cpp \
      solver.cpp \
      solver_progress.cpp \
      solver_types.cpp \
      variable_encoding.cpp \
      wcwidth.c \
      # Empty last line

include ../config.inc
include ../common

OBJ += ../util/util$(LIBEXT) \
       ../big-int/big-int$(LIBEXT) \
       ../goto-programs/goto-programs$(LIBEXT) \
       ../ansi-c/ansi-c$(LIBEXT) \
       ../linking/linking$(LIBEXT) \
       ../langapi/langapi$(LIBEXT) \
       ../solvers/solvers$(LIBEXT) \
       ../analyses/dirty$(OBJEXT) \
       ../analyses/does_remove_const$(OBJEXT) \
       ../analyses/locals$(OBJEXT) \
       ../analyses/local_bitvector_analysis$(OBJEXT) \
       ../analyses/local_cfg$(OBJEXT) \
       # Empty last line

INCLUDES= -I ..

LIBS = 

CLEANFILES = cprover$(EXEEXT)

all: cprover$(EXEEXT)

###############################################################################

cprover$(EXEEXT): $(OBJ)
	$(LINKBIN)

.PHONY: cprover-signed
cprover-signed: cprover$(EXEEXT)
	codesign -v -s $(OSX_IDENTITY) cprover$(EXEEXT)
