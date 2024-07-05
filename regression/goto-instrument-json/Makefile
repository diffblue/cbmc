default: tests.log

include ../../src/config.inc
include ../../src/common

test:
	@../test.pl -e -p -c '../chain.sh $(exe) ../../../src/symtab2gb/symtab2gb ../../../src/goto-instrument/goto-instrument'

tests.log:
	@../test.pl -e -p -c '../chain.sh $(exe) ../../../src/symtab2gb/symtab2gb ../../../src/goto-instrument/goto-instrument'

clean:
	$(RM) tests.log
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			cd "$$dir"; \
			$(RM) *.out *.gb; \
			cd ..; \
		fi \
	done
