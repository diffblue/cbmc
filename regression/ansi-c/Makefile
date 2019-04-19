default: tests.log

include ../../src/config.inc
include ../../src/common

ifeq ($(BUILD_ENV_),MSVC)
	exe=../../../src/goto-cc/goto-cl -X gcc-only
else
	exe=../../../src/goto-cc/goto-cc
endif

test:
	@../test.pl -e -p -c $(exe)
ifneq ($(BUILD_ENV_),MSVC)
	@../test.pl -e -p -c "$(exe) -xc++ -D_Bool=bool" -I test-c++-front-end -s c++-front-end
endif

tests.log: ../test.pl
	@../test.pl -e -p -c $(exe)
ifneq ($(BUILD_ENV_),MSVC)
	@../test.pl -e -p -c "$(exe) -xc++ -D_Bool=bool" -I test-c++-front-end -s c++-front-end
endif

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
