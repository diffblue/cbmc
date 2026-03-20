default: tests.log

include ../../src/config.inc
include ../../src/common

ifeq ($(BUILD_ENV_),MSVC)
	excluded_tests = -X gcc-only -X gcc-13
else
# gcc-13 tests require GCC 13+ libstdc++ headers
ifeq ($(wildcard /usr/include/c++/13),)
ifeq ($(wildcard /usr/include/c++/14),)
  excluded_tests += -X gcc-13
endif
endif
endif

test:
	@../test.pl -e -p -c "../../../src/cbmc/cbmc --validate-goto-model --validate-ssa-equation" $(excluded_tests) -X libcxx -X no-validate

tests.log: ../test.pl
	@../test.pl -e -p -c "../../../src/cbmc/cbmc --validate-goto-model --validate-ssa-equation" $(excluded_tests) -X libcxx -X no-validate

clean:
	find . -name '*.out' -execdir $(RM) '{}' \;
	find . -name '*.gb' -execdir $(RM) '{}' \;
	$(RM) tests.log
