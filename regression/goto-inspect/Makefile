default: tests.log

include ../../src/config.inc
include ../../src/common

ifeq ($(BUILD_ENV_),MSVC)
	exe=../../../src/goto-cc/goto-cl
	is_windows=true
	excluded_tests = -X winbug
else
	exe=../../../src/goto-cc/goto-cc
	is_windows=false
endif

test:
	@../test.pl -e -p -c '../chain.sh $(exe) ../../../src/goto-inspect/goto-inspect $(is_windows)' $(excluded_tests)

tests.log:
	@../test.pl -e -p -c '../chain.sh $(exe) ../../../src/goto-inspect/goto-inspect $(is_windows)' $(excluded_tests)

clean:
	find . -name '*.out' -execdir $(RM) '{}' \;
	find . -name '*.gb' -execdir $(RM) '{}' \;
	$(RM) tests.log
