default: tests.log

include ../../src/config.inc
include ../../src/common

bindir="$(pwd)../../../build/bin"
GOTO_CC="$(bindir)/goto-cc"
GOTO_INSTRUMENT="$(bindir)/goto-instrument"
CBMC="$(bindir)/cbmc"

ifeq ($(BUILD_ENV_),MSVC)
	exe=$(bindir)/goto-cl
else
	exe=$(bindir)/goto-cc
endif

test:
	@../test.pl -e -p -c '../rr.sh $(exe) $(GOTO_INSTRUMENT) $(CBMC)'

tests.log:
	@../test.pl -e -p -c '../rr.sh $(exe) $(GOTO_INSTRUMENT) $(CBMC)'

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
