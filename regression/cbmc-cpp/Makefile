default: tests.log

include ../../src/config.inc
include ../../src/common

ifeq ($(BUILD_ENV_),MSVC)
	excluded_tests = -X gcc-only
endif

# gcc-13 tests require GCC 13+ libstdc++ headers
GCC_VERSION := $(shell gcc -dumpversion 2>/dev/null)
GCC_MAJOR := $(firstword $(subst ., ,$(GCC_VERSION)))
ifeq ($(shell test "$(GCC_MAJOR)" -ge 13 2>/dev/null && echo yes),)
  excluded_tests += -X gcc-13
endif

test:
	@../test.pl -e -p -c "../../../src/cbmc/cbmc --validate-goto-model --validate-ssa-equation" $(excluded_tests) -X libcxx

tests.log: ../test.pl
	@../test.pl -e -p -c "../../../src/cbmc/cbmc --validate-goto-model --validate-ssa-equation" $(excluded_tests) -X libcxx

clean:
	find . -name '*.out' -execdir $(RM) '{}' \;
	find . -name '*.gb' -execdir $(RM) '{}' \;
	$(RM) tests.log
