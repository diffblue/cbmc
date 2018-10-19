SRC = dispatch_loop_detector.cpp

INCLUDES = -I .. -I . -I ../../src -I test-files

TEST_FILE_C = $(wildcard test-files/*.c)
TEST_FILE_S = $(patsubst test-files/%.c,test-files/%.c.string,$(TEST_FILE_C))

include ../../src/config.inc
include ../../src/common

CLEANFILES = dispatch-loop-detector$(OBJEXT)

.PHONY: all
all: dispatch-loop-detector$(OBJEXT)

dispatch-loop-detector$(OBJEXT): $(OBJ) $(TEST_FILE_S)
	$(LINKLIB)

test-files/%.c.string: test-files/%.c ../../scripts/make_string_literal.sh
	../../scripts/make_string_literal.sh dispatch $< $@
