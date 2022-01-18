default: test

test:
	@../test.pl -e -p -c "../../../unit/unit_tests"

tests.log: ../test.pl test

clean:
	$(RM) tests*.log
