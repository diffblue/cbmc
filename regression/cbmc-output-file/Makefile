default: tests.log

include ../../src/config.inc
include ../../src/common

test:
	@if which cvc5 ; then \
	  ../test.pl -f -e -p -c '../chain.py ../../../src/cbmc/cbmc' ; \
	fi

tests.log:
	@if which cvc5 ; then \
	  ../test.pl -f -e -p -c '../chain.py ../../../src/cbmc/cbmc' ; \
	fi

clean:
	@for dir in *; do \
		$(RM) tests.log; \
		if [ -d "$$dir" ]; then \
			cd "$$dir"; \
			$(RM) *.out *.gb; \
			cd ..; \
		fi \
	done
