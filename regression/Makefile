
DIRS = ansi-c \
       cbmc \
       cpp \
       cbmc-java \
       goto-analyzer \
       goto-instrument \
       goto-instrument-typedef \
       goto-trace \
       test-script \
       # Empty last line


test:
	$(foreach var,$(DIRS), $(MAKE) -C $(var) test || exit 1;)
