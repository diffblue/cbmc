DIRS = ansi-c \
       cbmc \
       cbmc-cover \
       cbmc-cpp \
       cbmc-java \
       cbmc-java-inheritance \
       cpp \
       goto-analyzer \
       goto-analyzer-taint \
       goto-cc-cbmc \
       goto-cc-goto-analyzer \
       goto-diff \
       goto-gcc \
       goto-instrument \
       goto-instrument-typedef \
       invariants \
       strings \
       jbmc-strings \
       strings-smoke-tests \
       test-script \
       # Empty last line

# Tests under goto-gcc cannot be run on Windows, so appveyor.yml unlinks
# the entire directory under Windows. This variable will contain the list
# of directories that actually exist on the current platform.
PLATFORM_DIRS = $(wildcard $(DIRS))

# Run all test directories in sequence
.PHONY: test
test:
	@for dir in $(PLATFORM_DIRS); do \
		$(MAKE) "$$dir" || exit 1; \
	done;

# Pattern to execute a single test suite directory
.PHONY: $(PLATFORM_DIRS)
$(PLATFORM_DIRS):
	@echo "Running $@..." ;
	$(MAKE) -C "$@" test || exit 1;

# Run all test directories using GNU Parallel
.PHONY: test-parallel
.NOTPARALLEL: test-parallel
test-parallel:
	@echo "Building with $(JOBS) jobs"
	parallel \
		--halt soon,fail=1 \
		--tag \
		--tagstring '{#}:' \
		--linebuffer \
		--jobs $(JOBS) \
		$(MAKE) "{}" \
		::: $(PLATFORM_DIRS)


.PHONY: clean
clean:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			$(MAKE) -C "$$dir" clean; \
		fi; \
	done;
