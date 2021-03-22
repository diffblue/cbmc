default: tests.log

include ../../src/config.inc
include ../../src/common

ifeq ($(BUILD_ENV_),MSVC)
	no_pthread = -X pthread
endif

test:
	@../test.pl -e -p -c ../../../src/cbmc/cbmc $(no_pthread)

tests.log: ../test.pl
	@../test.pl -e -p -c ../../../src/cbmc/cbmc $(no_pthread)

clean:
	find . -name '*.out' -execdir $(RM) '{}' \;
	$(RM) tests.log
