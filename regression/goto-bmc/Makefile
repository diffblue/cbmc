default: tests.log

test:
	@../test.pl -e -p -c ../../../src/goto-bmc/goto-bmc

tests.log: ../test.pl
	@../test.pl -e -p -c ../../../src/goto-bmc/goto-bmc

clean:
	find . -name '*.out' -execdir $(RM) '{}' \;
	find . -name '*.gb' -execdir $(RM) '{}' \;
	$(RM) tests.log
