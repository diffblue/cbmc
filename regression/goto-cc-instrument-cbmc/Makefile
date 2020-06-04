default: tests.log

include ../../src/config.inc
include ../../src/common

ifeq ($(BUILD_ENV_),MSVC)
	exe=../../../src/goto-cc/goto-cl
	is_windows=true
else
	exe=../../../src/goto-cc/goto-cc
	is_windows=false
endif

cbmc=../../../src/cbmc/cbmc
goto-instrument=../../../src/goto-instrument/goto-instrument

test:
	@../test.pl -e -p -c '../chain.sh $(exe) $(cbmc) $(goto-instrument) $(is_windows)'

tests.log:
	@../test.pl -e -p -c '../chain.sh $(exe) $(cbmc) $(goto-instrument) $(is_windows)'

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
