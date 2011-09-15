SRC = mode.cpp language_ui.cpp languages.cpp language_util.cpp

INCLUDES= -I .. -I ../util

include ../config.inc
include ../common

CLEANFILES = langapi$(LIBEXT)

all: langapi$(LIBEXT)

###############################################################################

langapi$(LIBEXT): $(OBJ)
	$(LINKLIB)
	
