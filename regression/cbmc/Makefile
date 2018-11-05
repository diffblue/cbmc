default: tests.log

test:
	@../test.pl -p -c ../../../src/cbmc/cbmc -X smt-backend

test-cprover-smt2:
	@../test.pl -p -c "../../../src/cbmc/cbmc --cprover-smt2"

tests.log: ../test.pl
	@../test.pl -p -c ../../../src/cbmc/cbmc -X smt-backend

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.c" "$$dir/*.out"; \
		fi; \
	done;

clean:
	find -name '*.out' -execdir $(RM) '{}' \;
	find -name '*.smt2' -execdir $(RM) '{}' \;
	$(RM) tests.log
