default: test

include ../../src/config.inc
include ../../src/common

ifeq ($(BUILD_ENV_),MSVC)
GCC_ONLY = -X gcc-only
else
GCC_ONLY =
endif

test:
	@../test.pl -e -p -c "../../../src/cbmc/cbmc --validate-goto-model --validate-ssa-equation" -X smt-backend $(GCC_ONLY)

test-cprover-smt2:
	@../test.pl -e -p -c "../../../src/cbmc/cbmc --cprover-smt2" \
					  -X broken-smt-backend -X thorough-smt-backend \
					  -X broken-cprover-smt-backend -X thorough-cprover-smt-backend \
					  -s cprover-smt2 $(GCC_ONLY)

test-z3:
	@../test.pl -e -p -c "../../../src/cbmc/cbmc --z3" \
					  -X broken-smt-backend -X thorough-smt-backend \
					  -X broken-z3-smt-backend -X thorough-z3-smt-backend \
					  -s z3 $(GCC_ONLY)

test-paths-lifo:
	@../test.pl -e -p -c "../../../src/cbmc/cbmc --paths lifo" \
					  -X thorough-paths -X smt-backend -X paths-lifo-expected-failure \
					  -s paths-lifo $(GCC_ONLY)

test-new-smt-backend:
	@../test.pl -e -p -c "../../../src/cbmc/cbmc --incremental-smt2-solver 'z3 --smt2 -in' --slice-formula" \
					  -I new-smt-backend \
					  -s new-smt-backend $(GCC_ONLY)

tests.log: ../test.pl test

clean:
	find . -name '*.out' -execdir $(RM) '{}' \;
	find . -name '*.smt2' -execdir $(RM) '{}' \;
	$(RM) tests*.log
