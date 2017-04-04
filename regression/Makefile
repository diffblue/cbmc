
DIRS = ansi-c \
       cbmc \
       cpp \
       cbmc-java \
       goto-instrument \
       test-script \
       # Empty last line


test:
	$(foreach var,$(DIRS), $(MAKE) -C $(var) test || exit 1;)
