SRC = language_util.cpp \
      language_file.cpp \
      language.cpp \
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
