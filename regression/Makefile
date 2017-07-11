DIRS = ansi-c \
       cbmc \
       cpp \
       cbmc-java \
       cbmc-java-inheritance \
       goto-analyzer \
       goto-instrument \
       goto-instrument-typedef \
       goto-diff \
       invariants \
       strings \
       strings-smoke-tests \
       test-script \
       # Empty last line


test:
	$(foreach var,$(DIRS), $(MAKE) -C $(var) test || exit 1;)

clean:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			$(MAKE) -C "$$dir" clean; \
		fi; \
	done;
