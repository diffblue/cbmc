default: test

test:
	@../test.pl -e -p -c "../../../unit/unit_tests"

tests.log: ../test.pl test

clean:
	find . -name '*.out' -execdir $(RM) '{}' \;
	$(RM) tests*.log
