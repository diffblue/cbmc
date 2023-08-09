default: test-no-p

include ../../src/config.inc
include ../../src/common

test:
	@../test.pl -e -p -c '../../../src/cprover/cprover'

test-no-p:
	@../test.pl -e -c '../../../src/cprover/cprover'

clean:
	find . -name '*.out' -execdir $(RM) '{}' \;
	$(RM) tests.log
