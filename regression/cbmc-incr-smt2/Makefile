default: test

include ../../src/config.inc
include ../../src/common

test:
	@../test.pl -e -p -c "../../../src/cbmc/cbmc --validate-goto-model --validate-ssa-equation --slice-formula"

tests.log: ../test.pl test

clean:
	find . -name '*.out' -execdir $(RM) '{}' \;
	find . -name '*.smt2' -execdir $(RM) '{}' \;
	$(RM) tests*.log
