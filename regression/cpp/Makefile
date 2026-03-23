default: tests.log

include ../../src/config.inc
include ../../src/common

ifeq ($(BUILD_ENV_),MSVC)
	exe = ../../../src/goto-cc/goto-cl
else
	exe = ../../../src/goto-cc/goto-cc
endif

ifeq ($(BUILD_ENV_),MSVC)
	excluded_tests = -X gcc-only
endif

test:
	@../test.pl -e -p -c $(exe) $(excluded_tests)
tests.log: ../test.pl
	@../test.pl -e -p -c $(exe) $(excluded_tests)

clean:
	find . -name '*.out' -execdir $(RM) '{}' \;
	find . -name '*.gb' -execdir $(RM) '{}' \;
	$(RM) tests.log
