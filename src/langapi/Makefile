SRC = language_ui.cpp \
      language_util.cpp \
      mode.cpp \
      # Empty last line
INCLUDES= -I ..

include ../config.inc
include ../common

CLEANFILES = langapi$(LIBEXT)

all: langapi$(LIBEXT)

###############################################################################

langapi$(LIBEXT): $(OBJ)
	$(LINKLIB)
