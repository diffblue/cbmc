SRC = symex_target.cpp symex_target_equation.cpp goto_symex.cpp \
      symex_main.cpp build_goto_trace.cpp adjust_float_expressions.cpp \
      symex_function_call.cpp goto_symex_state.cpp symex_dereference.cpp \
      symex_goto.cpp symex_builtin_functions.cpp slice.cpp symex_other.cpp \
      slice_by_trace.cpp symex_decl.cpp symex_dead.cpp rewrite_union.cpp \
      precondition.cpp postcondition.cpp symex_clean_expr.cpp \
      symex_dereference_state.cpp auto_objects.cpp ssa_expr.cpp \
      symex_catch.cpp symex_start_thread.cpp symex_assign.cpp \
      symex_throw.cpp symex_atomic_section.cpp memory_model.cpp \
      memory_model_sc.cpp partial_order_concurrency.cpp \
      memory_model_tso.cpp memory_model_pso.cpp

INCLUDES= -I ..

include ../config.inc
include ../common

CLEANFILES = goto-symex$(LIBEXT)

all: goto-symex$(LIBEXT)

###############################################################################

goto-symex$(LIBEXT): $(OBJ)
	$(LINKLIB)

