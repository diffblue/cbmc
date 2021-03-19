default: tests.log

test:
	@../test.pl -e -p -c ../../../src/solvers/smt2_solver

tests.log: ../test.pl
	@../test.pl -e -p -c ../../../src/solvers/smt2_solver

clean:
	find . -name '*.out' -execdir $(RM) '{}' \;
	$(RM) tests.log
