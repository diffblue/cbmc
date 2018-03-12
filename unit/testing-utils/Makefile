SRC = \
  c_to_expr.cpp \
  free_form_cmdline.cpp \
  load_java_class.cpp \
  require_expr.cpp \
  require_goto_statements.cpp \
  require_type.cpp \
  # Empty last line (please keep above list sorted!)

INCLUDES = -I .. -I . -I ../../src

include ../../src/config.inc
include ../../src/common

CLEANFILES = testing-utils$(LIBEXT)

.PHONY: all
all: testing-utils$(LIBEXT)

testing-utils$(LIBEXT): $(OBJ)
	$(LINKLIB)
