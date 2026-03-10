# For the best possible utilisation of multiple cores when
# running tests in parallel, it is important that these directories are
# listed with decreasing runtimes (i.e. longest running at the top)
DIRS = janalyzer \
       janalyzer-taint \
       jbmc \
       jbmc-concurrency \
       jbmc-inheritance \
       jbmc-json-ui \
       jbmc-strings \
       jdiff \
       strings-smoke-tests \
       jbmc-generics \
       # Empty last line

# Run all test directories in sequence
.PHONY: test
test:
	mvn --quiet clean package -T1C
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
	mvn --quiet clean package -T1C
	@echo "Building with $(JOBS) jobs"
	parallel \
		--halt soon,fail=1 \
		--tag \
		--tagstring '{#}:' \
		--linebuffer \
		--jobs $(JOBS) \
		$(MAKE) "{}" \
		::: $(DIRS)

# Run all test directories in parallel when invoked with make -j<N>
# (no GNU Parallel needed).
# Example: make -j8 test-parallel-jobs
# Without -j, the directories will run sequentially.
PARALLEL_DIRS = $(addprefix parallel__,$(DIRS))
.PHONY: mvn-package test-parallel-jobs $(PARALLEL_DIRS)
mvn-package:
	mvn --quiet clean package -T1C
test-parallel-jobs: $(PARALLEL_DIRS)
$(PARALLEL_DIRS): parallel__%: mvn-package
	@echo "Running $*..."
	$(MAKE) -C "$*" test


.PHONY: clean
clean:
	mvn --quiet clean -T1C
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			$(MAKE) -C "$$dir" clean; \
		fi; \
	done;
