default: test-no-p

include ../../../src/config.inc
include ../../../src/common

test:
	@../../test.pl -e -p -c '../../../../src/cprover/cprover --large-step'

test-no-p:
	@../../test.pl -e -c '../../../../src/cprover/cprover --large-step'

clean:
	find . -name '*.out' -execdir $(RM) '{}' \;
	$(RM) tests.log
