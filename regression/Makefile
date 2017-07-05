
DIRS = ansi-c \
       cbmc \
       cpp \
       cbmc-java \
       goto-analyzer \
       goto-gcc \
       goto-instrument \
       goto-instrument-typedef \
       test-script \
       # Empty last line


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
