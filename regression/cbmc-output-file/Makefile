default: tests.log

include ../../src/config.inc
include ../../src/common

EXCLUDED_TAGS =
ifeq ($(shell command -v cvc5 > /dev/null 2>&1 && echo found),)
  EXCLUDED_TAGS += -X cvc5
endif
ifeq ($(shell command -v z3 > /dev/null 2>&1 && echo found),)
  EXCLUDED_TAGS += -X z3
endif

test:
	@../test.pl -f -e -p -c '../chain.py ../../../src/cbmc/cbmc' $(EXCLUDED_TAGS)

tests.log:
	@../test.pl -f -e -p -c '../chain.py ../../../src/cbmc/cbmc' $(EXCLUDED_TAGS)

clean:
	$(RM) tests.log
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			cd "$$dir"; \
			$(RM) *.out *.gb; \
			cd ..; \
		fi \
	done
