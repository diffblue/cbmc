default: test

test:
	@../test.pl -e -p -c "../../../src/cbmc/cbmc --validate-goto-model --validate-ssa-equation" -X smt-backend

test-cprover-smt2:
	@../test.pl -e -p -c "../../../src/cbmc/cbmc --cprover-smt2" -X broken-smt-backend

test-paths-lifo:
	@../test.pl -e -p -c "../../../src/cbmc/cbmc --paths lifo" -X thorough-paths -X smt-backend -X paths-lifo-expected-failure

tests.log: ../test.pl test

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
