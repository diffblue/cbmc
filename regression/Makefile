DIRS = ansi-c \
       cbmc \
       cpp \
       cbmc-java \
       cbmc-java-inheritance \
       cbmc-cover \
       goto-analyzer \
       goto-diff \
       goto-gcc \
       goto-instrument \
       goto-instrument-typedef \
       invariants \
       strings \
       strings-smoke-tests \
       test-script \
       # Empty last line

# Check for the existence of $dir. Tests under goto-gcc cannot be run on
# Windows, so appveyor.yml unlinks the entire directory under Windows.
test:
	@for dir in $(DIRS); do \
	  if [ -d "$$dir" ]; then \
	    $(MAKE) -C "$$dir" test || exit 1; \
	  fi; \
	done;

clean:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			$(MAKE) -C "$$dir" clean; \
		fi; \
	done;
