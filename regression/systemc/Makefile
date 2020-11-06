ifneq ($(BUILD_ENV_),MSVC)
	# In MacOS, a change in the assert.h header file
	# is causing template errors when exercising the
	# C++ front end (because of a transitive include
	# of <type_traits>) for files that include the
	# <assert.h> or <cassert> headers.
	OS := $(shell uname)
	ifeq ($(OS),Darwin)
		excluded_tests = -X macos-assert-broken
	endif
endif

default: tests.log

test:
	@../test.pl -e -p -c "../../../src/cbmc/cbmc --validate-goto-model --validate-ssa-equation" $(excluded_tests)

tests.log: ../test.pl
	@../test.pl -e -p -c "../../../src/cbmc/cbmc --validate-goto-model --validate-ssa-equation" $(excluded_tests)

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.c" "$$dir/*.out"; \
		fi; \
	done;

clean:
	find -name '*.out' -execdir $(RM) '{}' \;
	find -name '*.gb' -execdir $(RM) '{}' \;
	$(RM) tests.log
