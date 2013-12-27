SRC = locs.cpp var_map.cpp

INCLUDES= -I ..

include ../config.inc
include ../common

CLEANFILES = path-symex$(LIBEXT)

all: path-symex$(LIBEXT)

###############################################################################

path-symex$(LIBEXT): $(OBJ)
	$(LINKLIB)

