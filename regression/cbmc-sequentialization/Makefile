default: test

include ../../src/config.inc
include ../../src/common

ifeq ($(BUILD_ENV_),MSVC)
POSIX_ONLY = -X requires_posix_only_headers
else
POSIX_ONLY =
endif

test:
	@../test.pl -e -p -c "../../../src/cbmc/cbmc --validate-goto-model --validate-ssa-equation" $(POSIX_ONLY)

tests.log: ../test.pl test

clean:
	find . -name '*.out' -execdir $(RM) '{}' \;
	find . -name '*.smt2' -execdir $(RM) '{}' \;
	$(RM) tests.log
