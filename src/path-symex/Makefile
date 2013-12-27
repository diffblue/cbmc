SRC = locs.cpp var_map.cpp path_symex_history.cpp path_symex_state.cpp \
      path_symex.cpp path_search.cpp

INCLUDES= -I ..

include ../config.inc
include ../common

CLEANFILES = path-symex$(LIBEXT)

all: path-symex$(LIBEXT)

###############################################################################

path-symex$(LIBEXT): $(OBJ)
	$(LINKLIB)

