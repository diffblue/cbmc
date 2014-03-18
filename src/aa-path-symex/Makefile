SRC = locs.cpp var_map.cpp path_symex_history.cpp path_symex_state.cpp \
      path_symex.cpp build_goto_trace.cpp

INCLUDES= -I ..

include ../config.inc
include ../common

CLEANFILES = aa-path-symex$(LIBEXT)

all: aa-path-symex$(LIBEXT)

###############################################################################

aa-path-symex$(LIBEXT): $(OBJ)
	$(LINKLIB)

