default: test

include ../../src/config.inc
include ../../src/common

ifeq ($(BUILD_ENV_),MSVC)
	exe=../../../src/goto-cc/goto-cl
	is_windows=true
	GCC_ONLY = -X gcc-only
else
	exe=../../../src/goto-cc/goto-cc
	is_windows=false
	GCC_ONLY =
endif

test:
	@../test.pl -e -p -c '../chain.sh $(exe) ../../../src/goto-instrument/goto-instrument ../../../src/cbmc/cbmc $(is_windows)' $(GCC_ONLY)

tests.log: ../test.pl test


clean:
	$(RM) tests.log
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			cd "$$dir"; \
			$(RM) *.out *.gb *.smt2; \
			cd ..; \
		fi \
	done
