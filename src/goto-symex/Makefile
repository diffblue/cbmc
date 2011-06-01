SRC = symex_target.cpp symex_target_equation.cpp basic_symex.cpp \
      symex_main.cpp goto_trace.cpp build_goto_trace.cpp \
      symex_function.cpp goto_symex_state.cpp symex_dereference.cpp \
      symex_goto.cpp builtin_functions.cpp slice.cpp symex_other.cpp \
      slice_by_trace.cpp xml_goto_trace.cpp symex_decl.cpp \
      precondition.cpp postcondition.cpp symex_clean_expr.cpp \
      symex_dereference_state.cpp vcd_goto_trace.cpp

OBJ = $(SRC:.cpp=$(OBJEXT))

INCLUDES= -I .. -I ../util

include ../config.inc
include ../common

all: goto-symex$(LIBEXT)

###############################################################################

goto-symex$(LIBEXT): $(OBJ)
	$(LINKLIB)

clean:
	rm -f $(OBJ) goto-symex$(LIBEXT)

