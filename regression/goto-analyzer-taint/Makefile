default: tests.log

test:
	@../test.pl -p -c ../../../src/goto-analyzer/goto-analyzer

tests.log: ../test.pl
	@../test.pl -p -c ../../../src/goto-analyzer/goto-analyzer

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.java" "$$dir/*.out"; \
		fi; \
	done;

clean:
	find -name '*.out' -execdir $(RM) '{}' \;
	find -name '*.gb' -execdir $(RM) '{}' \;
	$(RM) tests.log
