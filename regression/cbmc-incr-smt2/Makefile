default: test

include ../../src/config.inc
include ../../src/common

test: test.z3 test.cvc5

test.z3:
	@../test.pl -e -p -c "../../../src/cbmc/cbmc --incremental-smt2-solver 'z3 --smt2 -in' --validate-goto-model --validate-ssa-equation"

test.cvc5:
	@../test.pl -e -p -c "../../../src/cbmc/cbmc --incremental-smt2-solver 'cvc5 --lang=smtlib2.6 --incremental' --validate-goto-model --validate-ssa-equation"

tests.log: ../test.pl test

clean:
	find . -name '*.out' -execdir $(RM) '{}' \;
	find . -name '*.smt2' -execdir $(RM) '{}' \;
	$(RM) tests*.log
