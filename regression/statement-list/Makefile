default: test

test:
	@../test.pl -e -p -c "../../../src/cbmc/cbmc" -X smt-backend

tests.log: ../test.pl test

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.awl" "$$dir/*.out"; \
		fi; \
	done;

clean:
	find -name '*.out' -execdir $(RM) '{}' \;
	find -name '*.smt2' -execdir $(RM) '{}' \;
	$(RM) tests.log
