default: test

include ../../src/config.inc
include ../../src/common

test:
	@../test.pl -e -p -c ../../../src/cbmc/cbmc
	@bash test_sarif_valid.sh ../../src/cbmc/cbmc

tests.log: ../test.pl test

clean:
	find . -name '*.out' -execdir $(RM) '{}' \;
	$(RM) tests*.log
