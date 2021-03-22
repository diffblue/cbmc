default: tests.log

include ../../src/config.inc
include ../../src/common

ifeq ($(BUILD_ENV_),MSVC)
	exe=../../../src/goto-cc/goto-cl
	is_windows=true
	exclude_broken_windows_tests=-X winbug
else
	exe=../../../src/goto-cc/goto-cc
	is_windows=false
	exclude_broken_windows_tests=
endif

test:
	@../test.pl -e -p -c '../chain.sh $(exe) ../../../src/cbmc/cbmc $(is_windows)' $(exclude_broken_windows_tests)

tests.log:
	@../test.pl -e -p -c '../chain.sh $(exe) ../../../src/cbmc/cbmc $(is_windows)' $(exclude_broken_windows_tests)

clean:
	@for dir in *; do \
		$(RM) tests.log; \
		if [ -d "$$dir" ]; then \
			cd "$$dir"; \
			$(RM) *.out *.gb; \
			cd ..; \
		fi \
	done
