SRC = mode.cpp language_ui.cpp languages.cpp language_util.cpp

OBJ = $(SRC:.cpp=$(OBJEXT))

INCLUDES= -I .. -I ../util

include ../config.inc
include ../common

all: langapi$(LIBEXT)

###############################################################################

langapi$(LIBEXT): $(OBJ)
	$(LINKLIB)
	
clean:
	rm -f $(OBJ) langapi$(LIBEXT)
	

