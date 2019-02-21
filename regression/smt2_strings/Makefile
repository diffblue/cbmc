default: tests.log

test:
	@../test.pl -e -p -c ../../../src/solvers/smt2_solver

tests.log: ../test.pl
	@../test.pl -e -p -c ../../../src/solvers/smt2_solver

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.c" "$$dir/*.out"; \
		fi; \
	done;

clean:
	find -name '*.out' -execdir $(RM) '{}' \;
	$(RM) tests.log
