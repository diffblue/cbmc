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

# Suites whose long-running symex-driven-lazy-loading profile is split into
# shards so it parallelises across workers instead of running as a single job
# (mirrors the ctest sharding in the CMake build). Each *_SHARDS value lists
# the shard indices; the shard count is the number of indices.
SHARDED_DIRS = jbmc-strings jbmc strings-smoke-tests
jbmc-strings_SHARDS = 1 2 3 4
jbmc_SHARDS = 1 2 3
strings-smoke-tests_SHARDS = 1 2

# Expand the directory list into parallel "jobs": non-sharded directories run
# as a single job (make -C <dir> test); each sharded directory contributes one
# job for its non-sdll tests (<dir>@normal) plus one job per sdll shard
# (<dir>@<index>@<count>). The job name encodes the work; the rules below parse
# it. This keeps the longest suites from serialising a whole worker.
PLAIN_DIRS = $(filter-out $(SHARDED_DIRS),$(DIRS))
NORMAL_JOBS = $(foreach d,$(SHARDED_DIRS),$(d)@normal)
SDLL_JOBS = $(foreach d,$(SHARDED_DIRS),\
              $(foreach i,$($(d)_SHARDS),$(d)@$(i)@$(words $($(d)_SHARDS))))
PARALLEL_JOBS = $(PLAIN_DIRS) $(NORMAL_JOBS) $(SDLL_JOBS)

.PHONY: $(NORMAL_JOBS)
$(NORMAL_JOBS):
	@suite=`echo "$@" | cut -d@ -f1`; \
	echo "Running $$suite (non-sdll tests)..."; \
	$(MAKE) -C "$$suite" test-normal

.PHONY: $(SDLL_JOBS)
$(SDLL_JOBS):
	@suite=`echo "$@" | cut -d@ -f1`; \
	idx=`echo "$@" | cut -d@ -f2`; \
	cnt=`echo "$@" | cut -d@ -f3`; \
	echo "Running $$suite (symex-driven-lazy-loading shard $$idx/$$cnt)..."; \
	$(MAKE) -C "$$suite" test-symex-driven-lazy-loading SHARD=$$idx/$$cnt

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
		::: $(PARALLEL_JOBS)

# Run all test directories in parallel when invoked with make -j<N>
# (no GNU Parallel needed).
# Example: make -j8 test-parallel-jobs
# Without -j, the directories will run sequentially.
PARALLEL_JOB_TARGETS = $(addprefix parallel__,$(PARALLEL_JOBS))
.PHONY: mvn-package test-parallel-jobs $(PARALLEL_JOB_TARGETS)
mvn-package:
	mvn --quiet clean package -T1C
test-parallel-jobs: $(PARALLEL_JOB_TARGETS)
# Run each job only after mvn-package has produced the jars; the work happens
# in a recursive make of the bare job goal (whose recipe has no mvn-package
# prerequisite, so the same goals are reusable by the GNU Parallel path above).
$(PARALLEL_JOB_TARGETS): parallel__%: mvn-package
	+$(MAKE) $*


.PHONY: clean
clean:
	mvn --quiet clean -T1C
	rm -rf jbmc/classpath-class-incorrect-package/incorrect-classes
	rm -rf jbmc/classpath-class-with-one-dir/default-classes
	rm -f jbmc/overlay-class/Test.class
	rm -f jbmc/overlay-class/annotations/org/cprover/*.class
	rm -f jbmc/overlay-class/correct-overlay/Test.class
	rm -f jbmc/overlay-class/ignored-method/Test.class
	rm -f jbmc/overlay-class/unmarked-overlay/Test.class
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			$(MAKE) -C "$$dir" clean; \
		fi; \
	done;
