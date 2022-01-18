# For the best possible utilisation of multiple cores when
# running tests in parallel, it is important that these directories are
# listed with decreasing runtimes (i.e. longest running at the top)
DIRS = cbmc \
       cbmc-library \
       crangler \
       goto-analyzer \
       ansi-c \
       goto-instrument \
       cpp \
       cbmc-concurrency \
       cbmc-cover \
       cbmc-incr-oneloop \
       cbmc-incr-smt2 \
       cbmc-incr \
       cbmc-with-incr \
       array-refinement-with-incr \
       goto-instrument-json \
       goto-instrument-wmm-core \
       goto-instrument-typedef \
       smt2_solver \
       smt2_strings \
       strings \
       invariants \
       goto-diff \
       test-script \
       goto-analyzer-taint \
       goto-gcc \
       goto-cl \
       goto-cc-cbmc \
       goto-cc-cbmc-shared-options \
       cbmc-cpp \
       goto-cc-goto-analyzer \
       goto-analyzer-simplify \
       statement-list \
       systemc \
       contracts \
       acceleration \
       k-induction \
       goto-harness \
       goto-harness-multi-file-project \
       goto-cc-file-local \
       goto-cc-regression-gh-issue-5380 \
       linking-goto-binaries \
       symtab2gb \
       symtab2gb-cbmc \
       solver-hardness \
       goto-ld \
       validate-trace-xml-schema \
       cbmc-primitives \
       goto-interpreter \
       cbmc-sequentialization \
       cpp-linter \
       catch-framework \
       # Empty last line

ifeq ($(OS),Windows_NT)
    detected_OS := Windows
else
    detected_OS := $(shell sh -c 'uname 2>/dev/null || echo Unknown')
endif

ifeq ($(detected_OS),Linux)
  ifneq ($(WITH_MEMORY_ANALYZER),0)
    # only set if it wasn't explicitly unset
    WITH_MEMORY_ANALYZER=1
  endif
endif

ifeq ($(WITH_MEMORY_ANALYZER),1)
  DIRS += snapshot-harness \
          memory-analyzer \
          extract_type_header
endif

# Run all test directories in sequence
.PHONY: test
test:
	@for dir in $(DIRS); do \
		$(MAKE) "$$dir" || exit 1; \
	done;

# Pattern to execute a single test suite directory
.PHONY: $(DIRS)
$(DIRS):
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
		::: $(DIRS)


.PHONY: clean
clean:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			$(MAKE) -C "$$dir" clean; \
		fi; \
	done;
	$(RM) tests.log
