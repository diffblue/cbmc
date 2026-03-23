default: tests.log

include ../../src/config.inc
include ../../src/common

ifeq ($(BUILD_ENV_),MSVC)
	excluded_tests = -X gcc-only
endif

test:
	@../test.pl -e -p -c "../../../src/cbmc/cbmc --validate-goto-model --validate-ssa-equation" $(excluded_tests) -X libcxx -X no-validate

tests.log: ../test.pl
	@../test.pl -e -p -c "../../../src/cbmc/cbmc --validate-goto-model --validate-ssa-equation" $(excluded_tests) -X libcxx -X no-validate

clean:
	find . -name '*.out' -execdir $(RM) '{}' \;
	find . -name '*.gb' -execdir $(RM) '{}' \;
	$(RM) tests.log
