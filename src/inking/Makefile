SRC = inking.cpp \
      remove_internal_symbols.cpp \
      static_lifetime_init.cpp \
      zero_initializer.cpp \
      # Empty last line

INCLUDES= -I ..

include ../config.inc
include ../common

CLEANFILES = inking$(LIBEXT)

all: inking$(LIBEXT)

###############################################################################

inking$(LIBEXT): $(OBJ)
	$(LINKLIB)
