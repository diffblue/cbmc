default: tests.log

test:
	@../test.pl -e -p -c "../chain.sh ../../../src/goto-analyzer/goto-analyzer --no-standard-checks"

tests.log: ../test.pl
	@../test.pl -e -p -c "../chain.sh ../../../src/goto-analyzer/goto-analyzer --no-standard-checks"

clean:
	find . -name '*.out' -execdir $(RM) '{}' \;
	find . -name '*.gb' -execdir $(RM) '{}' \;
	$(RM) tests.log
