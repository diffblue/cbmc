default: tests.log

# Paths are relative to each test subdirectory (regression/cbmc-pass-by-value/*/).
CHECKER=../../../scripts/check-pass-by-value

test:
	@../test.pl -p -c "../chain.sh $(CHECKER)"

tests.log: ../test.pl
	@../test.pl -p -c "../chain.sh $(CHECKER)"

clean:
	find . -name '*.out' -execdir $(RM) '{}' \;
	$(RM) tests.log
