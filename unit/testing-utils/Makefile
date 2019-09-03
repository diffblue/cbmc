SRC = \
  call_graph_test_utils.cpp \
  free_form_cmdline.cpp \
  invariant.cpp \
  message.cpp \
  require_expr.cpp \
  require_symbol.cpp \
  run_test_with_compilers.cpp \
  # Empty last line (please keep above list sorted!)

INCLUDES = -I .. -I . -I ../../src

include ../../src/config.inc
include ../../src/common

CLEANFILES = testing-utils$(LIBEXT)

.PHONY: all
all: testing-utils$(LIBEXT)

testing-utils$(LIBEXT): $(OBJ)
	$(LINKLIB)
