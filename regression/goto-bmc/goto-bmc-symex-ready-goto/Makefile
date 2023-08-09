default: tests.log

CBMC_EXE=../../../../src/cbmc/cbmc
GOTO_BMC_EXE=../../../../src/goto-bmc/goto-bmc

test:
	@../../test.pl -e -p -c "../chain.sh $(CBMC_EXE) $(GOTO_BMC_EXE)"

tests.log: ../test.pl
	@../../test.pl -e -p -c "../chain.sh $(CBMC_EXE) $(GOTO_BMC_EXE)"

clean:
	find . -name '*.out' -execdir $(RM) '{}' \;
	find . -name '*.gb' -execdir $(RM) {} \;
	$(RM) tests.log
