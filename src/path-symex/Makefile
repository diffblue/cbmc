SRC = locs.cpp var_map.cpp path_symex_history.cpp path_symex_state.cpp \
      path_symex.cpp build_goto_trace.cpp path_replay.cpp \
      path_symex_state_read.cpp \
      path_symex_taint_data.cpp \
      path_symex_taint_analysis.cpp \
	  path_symex_taint_parser.cpp
	  
INCLUDES= -I ..

include ../config.inc
include ../common

CLEANFILES = path-symex$(LIBEXT)

all: path-symex$(LIBEXT)

###############################################################################

path-symex$(LIBEXT): $(OBJ)
	$(LINKLIB)

