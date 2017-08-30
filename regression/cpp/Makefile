default: tests.log

include ../../src/config.inc
include ../../src/common

ifeq ($(BUILD_ENV_),MSVC)
	exe=../../../src/goto-cc/goto-cl
else
	exe=../../../src/goto-cc/goto-cc
endif

test:
	@if ! ../test.pl -c $(exe) ; then \
		../failed-tests-printer.pl ; \
		exit 1 ; \
	fi

tests.log: ../test.pl
	@if ! ../test.pl -c $(exe) ; then \
		../failed-tests-printer.pl ; \
		exit 1 ; \
	fi

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
