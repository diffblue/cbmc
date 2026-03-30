default: tests.log

include ../../src/config.inc
include ../../src/common

ifeq ($(BUILD_ENV_),MSVC)
  excluded_tests = -X gcc-only
endif

# On non-MSVC, detect if the compiler is GCC (Free Software Foundation)
# or something else (Clang, Apple Clang). Exclude gcc-only on non-GCC.
ifndef excluded_tests
  IS_GCC := $(shell gcc --version 2>&1 | grep -c 'Free Software Foundation')
  ifeq ($(IS_GCC),0)
    excluded_tests = -X gcc-only
  endif
endif

test:
	@../test.pl -e -p -c "../../../src/cbmc/cbmc --validate-goto-model --validate-ssa-equation" $(excluded_tests) -X libcxx

tests.log: ../test.pl
	@../test.pl -e -p -c "../../../src/cbmc/cbmc --validate-goto-model --validate-ssa-equation" $(excluded_tests) -X libcxx

clean:
	find . -name '*.out' -execdir $(RM) '{}' \;
	find . -name '*.gb' -execdir $(RM) '{}' \;
	$(RM) tests.log
