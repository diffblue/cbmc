SRC = auto_objects.cpp \
      build_goto_trace.cpp \
      goto_symex.cpp \
      goto_symex_state.cpp \
      memory_model.cpp \
      memory_model_pso.cpp \
      memory_model_sc.cpp \
      memory_model_tso.cpp \
      partial_order_concurrency.cpp \
      path_storage.cpp \
      postcondition.cpp \
      precondition.cpp \
      show_program.cpp \
      show_vcc.cpp \
      slice.cpp \
      slice_by_trace.cpp \
      symex_assign.cpp \
      symex_atomic_section.cpp \
      symex_builtin_functions.cpp \
      symex_catch.cpp \
      symex_clean_expr.cpp \
      symex_dead.cpp \
      symex_decl.cpp \
      symex_dereference.cpp \
      symex_dereference_state.cpp \
      symex_function_call.cpp \
      symex_goto.cpp \
      symex_main.cpp \
      symex_other.cpp \
      symex_start_thread.cpp \
      symex_target.cpp \
      symex_target_equation.cpp \
      symex_throw.cpp \
      # Empty last line

INCLUDES= -I ..

include ../config.inc
include ../common

CLEANFILES = goto-symex$(LIBEXT)

all: goto-symex$(LIBEXT)

###############################################################################

goto-symex$(LIBEXT): $(OBJ)
	$(LINKLIB)
