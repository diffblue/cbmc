default: clean tests.log

GOTO_GCC_EXE=../../../src/goto-cc/goto-gcc
MEMORY_ANALYZER_EXE=../../../src/memory-analyzer/memory-analyzer

clean:
	find . -name '*.gb' -execdir $(RM) '{}' \;
	find . -name '*.exe' -execdir $(RM) '{}' \;
	find . -name '*.out' -execdir $(RM) '{}' \;
	$(RM) tests.log

test:
	@../test.pl -e -p -c "../chain.sh $(MEMORY_ANALYZER_EXE) $(GOTO_GCC_EXE)"

tests.log: ../test.pl
	@../test.pl -e -p -c "../chain.sh $(MEMORY_ANALYZER_EXE) $(GOTO_GCC_EXE)"
