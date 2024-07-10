default: tests.log

include ../../src/config.inc
include ../../src/common

test:
	@../test.pl -e -p -c '../chain.sh $(exe) ../../../src/symtab2gb/symtab2gb ../../../src/cbmc/cbmc'

tests.log:
	@../test.pl -e -p -c '../chain.sh $(exe) ../../../src/symtab2gb/symtab2gb ../../../src/cbmc/cbmc'

clean:
	$(RM) tests.log
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			cd "$$dir"; \
			$(RM) *.out *.gb; \
			cd ..; \
		fi \
	done
