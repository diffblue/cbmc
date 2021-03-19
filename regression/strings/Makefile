default: tests.log

test:
	@../test.pl -e -p -c ../../../src/cbmc/cbmc

testfuture:
	@../test.pl -e -p -c ../../../src/cbmc/cbmc -CF

testall:
	@../test.pl -e -p -c ../../../src/cbmc/cbmc -CFTK

tests.log: ../test.pl
	@../test.pl -e -p -c ../../../src/cbmc/cbmc

clean:
	find . -name '*.out' -execdir $(RM) '{}' \;
	find . -name '*.gb' -execdir $(RM) '{}' \;
	$(RM) tests.log

