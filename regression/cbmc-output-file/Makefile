default: tests.log

include ../../src/config.inc
include ../../src/common

test:
	@../test.pl -f -e -p -c '../chain.py ../../../src/cbmc/cbmc'

tests.log:
	@../test.pl -f -e -p -c '../chain.py ../../../src/cbmc/cbmc'

clean:
	@for dir in *; do \
		$(RM) tests.log; \
		if [ -d "$$dir" ]; then \
			cd "$$dir"; \
			$(RM) *.out *.gb; \
			cd ..; \
		fi \
	done
