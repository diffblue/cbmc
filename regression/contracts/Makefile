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
	@../test.pl -e -p -c '../chain.sh $(exe) ../../../src/goto-instrument/goto-instrument ../../../src/cbmc/cbmc $(is_windows)' -X smt-backend $(GCC_ONLY)

test-cprover-smt2:
	@../test.pl -e -p -c '../chain.sh $(exe) ../../../src/goto-instrument/goto-instrument "../../../src/cbmc/cbmc --cprover-smt2" $(is_windows)' \
					  -X broken-smt-backend -X thorough-smt-backend \
					  -X broken-cprover-smt-backend -X thorough-cprover-smt-backend \
					  -s cprover-smt2 $(GCC_ONLY)

test-z3:
	@../test.pl -e -p -c '../chain.sh $(exe) ../../../src/goto-instrument/goto-instrument "../../../src/cbmc/cbmc --z3" $(is_windows)' \
					  -X broken-smt-backend -X thorough-smt-backend \
					  -X broken-z3-smt-backend -X thorough-z3-smt-backend \
					  -s z3 $(GCC_ONLY)

tests.log: ../test.pl test


clean:
	@for dir in *; do \
		$(RM) tests.log; \
		if [ -d "$$dir" ]; then \
			cd "$$dir"; \
			$(RM) *.out *.gb *.smt2; \
			cd ..; \
		fi \
	done
