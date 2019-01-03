# For the best possible utilisation of multiple cores when
# running tests in parallel, it is important that these directories are
# listed with decreasing runtimes (i.e. longest running at the top)
DIRS = cbmc \
       cbmc-library \
       goto-analyzer \
       ansi-c \
       goto-instrument \
       cpp \
       cbmc-cover \
       goto-instrument-typedef \
       smt2_solver \
       strings \
       invariants \
       goto-diff \
       test-script \
       goto-analyzer-taint \
       goto-gcc \
       goto-cl \
       goto-cc-cbmc \
       cbmc-cpp \
       goto-cc-goto-analyzer \
       systemc \
       contracts \
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
