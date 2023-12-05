default: tests.log

test:
	@../test.pl -e -p -c "../../../src/cbmc/cbmc --no-standard-checks"

test.smt2_incr:
	@../test.pl -e -p -X no-new-smt -c "../../../src/cbmc/cbmc --no-standard-checks --incremental-smt2-solver 'z3 --smt2 -in' --validate-goto-model --validate-ssa-equation"

tests.log: ../test.pl
	@../test.pl -e -p -c "../../../src/cbmc/cbmc --no-standard-checks"

clean:
	find . -name '*.out' -execdir $(RM) '{}' \;
	$(RM) tests*.log
