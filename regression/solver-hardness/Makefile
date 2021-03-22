default: tests.log

include ../../src/config.inc
include ../../src/common

CBMC_EXE=../../../src/cbmc/cbmc

test:
ifeq (, $(shell which jq))
	echo "solver-hardness tests skipped (can't find 'jq' in your path)"
else
	@../test.pl -e -p -c "../chain.sh $(CBMC_EXE)"
endif

tests.log: ../test.pl test

clean:
	find . -name '*.out' -execdir $(RM) '{}' \;
	$(RM) tests.log
