default: tests.log

include ../../src/config.inc
include ../../src/common

ifeq ($(BUILD_ENV_),MSVC)
test:

tests.log:

else
test:
	@../test.pl -e -p -c '../../../src/crangler/crangler'

tests.log:
	@../test.pl -e -p -c '../../../src/crangler/crangler'
endif

clean:
	$(RM) tests.log
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			cd "$$dir"; \
			$(RM) *.out *.gb; \
			cd ..; \
		fi \
	done
