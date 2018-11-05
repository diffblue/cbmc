SRC = path_strategies.cpp

INCLUDES = -I .. -I . -I ../../src -I test-files

TEST_FILE_C = $(wildcard test-files/*.c)
TEST_FILE_S = $(patsubst test-files/%.c,test-files/%.c.string,$(TEST_FILE_C))

include ../../src/config.inc
include ../../src/common

CLEANFILES = path_strategies$(OBJEXT)

.PHONY: all
all: path_strategies$(OBJEXT)

path_strategies$(OBJEXT): $(OBJ) $(TEST_FILE_S)
	$(LINKLIB)

test-files/%.c.string: test-files/%.c ../../scripts/make_string_literal.sh
	../../scripts/make_string_literal.sh path-strategy $< $@
