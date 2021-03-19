default: tests.log

TOOL = "../../../src/cbmc/cbmc --incremental"

test:
	@../test.pl -c $(TOOL)

tests.log: ../test.pl
	@../test.pl -c $(TOOL)

clean:
	find . -name '*.out' -execdir $(RM) '{}' \;
	find . -name '*.gb' -execdir $(RM) '{}' \;
	$(RM) tests.log
