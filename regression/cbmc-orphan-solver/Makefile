default: tests.log

include ../../src/config.inc
include ../../src/common

test:
	@../test.pl -e -p -c './chain.sh'

tests.log: ../test.pl test

clean:
	$(RM) tests.log

