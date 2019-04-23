default: tests.log

include ../../src/config.inc
include ../../src/common

ifeq ($(BUILD_ENV_),MSVC)
	gcc_only = -X gcc-only
else
	gcc_only =
endif

test:
	@../test.pl -e -p -c "../../../src/cbmc/cbmc --validate-goto-model --validate-ssa-equation" $(gcc_only)

tests.log: ../test.pl
	@../test.pl -e -p -c "../../../src/cbmc/cbmc --validate-goto-model --validate-ssa-equation" $(gcc_only)

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.c" "$$dir/*.out"; \
		fi; \
	done;

clean:
	find -name '*.out' -execdir $(RM) '{}' \;
	find -name '*.gb' -execdir $(RM) '{}' \;
	$(RM) tests.log
