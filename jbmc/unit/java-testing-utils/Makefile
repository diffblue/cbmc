SRC = \
  load_java_class.cpp \
  require_goto_statements.cpp \
  require_parse_tree.cpp \
  require_type.cpp \
  # Empty last line (please keep above list sorted!)

INCLUDES = -I .. -I . -I ../../src -I ../$(CPROVER_DIR)/src -I ../$(CPROVER_DIR)/unit

include ../../src/config.inc
include ../$(CPROVER_DIR)/src/config.inc
include ../$(CPROVER_DIR)/src/common

CLEANFILES = java-testing-utils$(LIBEXT)

.PHONY: all
all: java-testing-utils$(LIBEXT)

java-testing-utils$(LIBEXT): $(OBJ)
	$(LINKLIB)
