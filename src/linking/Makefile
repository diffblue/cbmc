SRC = linking.cpp zero_initializer.cpp static_lifetime_init.cpp \
      remove_internal_symbols.cpp

INCLUDES= -I ..

include ../config.inc
include ../common

CLEANFILES = linking$(LIBEXT)

all: linking$(LIBEXT)

###############################################################################

linking$(LIBEXT): $(OBJ)
	$(LINKLIB)
