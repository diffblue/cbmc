SRC = mode.cpp language_ui.cpp languages.cpp language_util.cpp

INCLUDES= -I ..

include ../config.inc
include ../common

CLEANFILES = langapi$(LIBEXT)

all: langapi$(LIBEXT)

###############################################################################

langapi$(LIBEXT): $(OBJ)
	$(LINKLIB)
	
