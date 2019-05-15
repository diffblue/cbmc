default: tests.log

include ../../src/config.inc
include ../../src/common

test:
	@../test.pl -e -p -c '../chain.sh $(exe) ../../../src/symtab2gb/symtab2gb ../../../src/cbmc/cbmc'

tests.log:
	@../test.pl -e -p -c '../chain.sh $(exe) ../../../src/symtab2gb/symtab2gb ../../../src/cbmc/cbmc'

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.c" "$$dir/*.out"; \
		fi; \
	done;

clean:
	@for dir in *; do \
		$(RM) tests.log; \
		if [ -d "$$dir" ]; then \
			cd "$$dir"; \
			$(RM) *.out *.gb; \
			cd ..; \
		fi \
	done
