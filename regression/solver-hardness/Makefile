default: tests.log

include ../../src/config.inc
include ../../src/common

CBMC_EXE=../../../src/cbmc/cbmc

test:
	@../test.pl -e -p -c "../chain.sh $(CBMC_EXE)"

tests.log: ../test.pl
	@../test.pl -e -p -c "../chain.sh $(CBMC_EXE)"

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.c" "$$dir/*.out"; \
		fi; \
	done;

clean:
	find -name '*.out' -execdir $(RM) '{}' \;
	$(RM) tests.log
