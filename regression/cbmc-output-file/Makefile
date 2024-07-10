default: tests.log

include ../../src/config.inc
include ../../src/common

test:
	@../test.pl -f -e -p -c '../chain.py ../../../src/cbmc/cbmc'

tests.log:
	@../test.pl -f -e -p -c '../chain.py ../../../src/cbmc/cbmc'

clean:
	$(RM) tests.log
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			cd "$$dir"; \
			$(RM) *.out *.gb; \
			cd ..; \
		fi \
	done
