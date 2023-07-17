default: tests.log

test:
	@../../test.pl -e -p -c ../../api-binary-driver

tests.log:
	@../../test.pl -e -p -c ../../api-binary-driver

clean:
	find . -name '*.out' -execdir $(RM) '{}' \;
	find . -name '*.gb' -execdir $(RM) '{}' \;
	$(RM) tests.log
