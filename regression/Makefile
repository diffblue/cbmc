DIRS = ansi-c \
       cbmc \
       cpp \
       cbmc-java \
       cbmc-java-inheritance \
       goto-analyzer \
       goto-diff \
       goto-instrument \
       goto-instrument-typedef \
       invariants \
       strings \
       strings-smoke-tests \
       test-script \
       # Empty last line

.DEFAULT_GOAL := test

# How many cores are available
# Windows not supported = 1
# CI has an issue with reporting correct number
# `getconf _NPROCESSORS_ONLN` works on Linux and OS X
ifeq ($(OS),Windows_NT)
	NJOB = 1
else
  ifdef CI
  	NJOB = 2
  else
    NJOB = $(shell getconf _NPROCESSORS_ONLN)
  endif
endif

test:
	$(foreach var,$(DIRS), $(MAKE) -C $(var) test || exit 1;)

###############################################################################
# Run tests using GNU parallel 20170722 or above
# `make -C regression test-parallel`
#
# Prereq:
# - Install GNU parallel:
#   - ubuntu
#   	(wget -O - pi.dk/3 || curl pi.dk/3/ || \
#     fetch -o - http://pi.dk/3) | bash
#   - osx
#			brew install parallel
###############################################################################
test-parallel:
	parallel --halt now,fail=1 \
		--jobs $(NJOB) \
		--bar \
		--joblog regression.stats \
		$(MAKE) -C {} test \
		::: $(DIRS)
	cat regression.stats

clean:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			$(MAKE) -C "$$dir" clean; \
		fi; \
	done;
