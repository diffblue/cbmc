default: tests.log

test:
	@../test.pl -e -p -c '../goto-cc-modes/modes.sh ../../../src/goto-cc/goto-cc'

tests.log: ../test.pl
	@../test.pl -e -p -c '../goto-cc-modes/modes.sh ../../../src/goto-cc/goto-cc'

clean:
	find . -name '*.out' -execdir $(RM) '{}' \;
	find . -name '*.obj' -execdir $(RM) '{}' \;
	$(RM) tests.log
