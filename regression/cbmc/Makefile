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
	@../test.pl -e -p -c "../../../src/cbmc/cbmc --cprover-smt2" -X broken-smt-backend $(GCC_ONLY)

test-paths-lifo:
	@../test.pl -e -p -c "../../../src/cbmc/cbmc --paths lifo" -X thorough-paths -X smt-backend -X paths-lifo-expected-failure $(GCC_ONLY)

tests.log: ../test.pl test

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.c" "$$dir/*.out"; \
		fi; \
	done;

clean:
	find -name '*.out' -execdir $(RM) '{}' \;
	find -name '*.smt2' -execdir $(RM) '{}' \;
	$(RM) tests.log
