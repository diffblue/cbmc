default: test

test:
	@../test.pl -e -p -c "../chain.sh \
		../../../src/goto-cc/goto-cc \
	  ../../../src/goto-harness/goto-harness \
		../../../src/cbmc/cbmc"
clean:
	find -name '*.out' -execdir $(RM) '{}' \;
	$(RM) tests.log
