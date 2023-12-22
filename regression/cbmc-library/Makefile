default: tests.log

include ../../src/config.inc
include ../../src/common

ifeq ($(BUILD_ENV_),MSVC)
	unix_only = -X unix
	gcc_only = -X gcc-only
endif

test:
	@../test.pl -e -p -c ../../../src/cbmc/cbmc $(unix_only) $(gcc_only)

tests.log: ../test.pl
	@../test.pl -e -p -c ../../../src/cbmc/cbmc $(unix_only) $(gcc_only)

clean:
	find . -name '*.out' -execdir $(RM) '{}' \;
	$(RM) tests.log
