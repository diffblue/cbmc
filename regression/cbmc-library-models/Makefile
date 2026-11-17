default: tests.log

include ../../src/config.inc
include ../../src/common

test:
	@../test.pl -e -p -c '../chain.sh ../../../src/cbmc/cbmc'

tests.log:
	@../test.pl -e -p -c '../chain.sh ../../../src/cbmc/cbmc'

clean:
	$(RM) tests.log
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			$(RM) -r "$$dir"/*.out "$$dir"/models.dir; \
		fi \
	done
