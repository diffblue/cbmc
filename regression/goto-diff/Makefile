default: tests.log

test:
	@../test.pl -e -p -c ../../../src/goto-diff/goto-diff

tests.log: ../test.pl
	@../test.pl -e -p -c ../../../src/goto-diff/goto-diff

clean:
	find . -name '*.out' -execdir $(RM) '{}' \;
	$(RM) tests.log
