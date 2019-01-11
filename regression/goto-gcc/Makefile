default: tests.log

include ../../src/config.inc
include ../../src/common

ifeq ($(BUILD_ENV_),MSVC)
test:

tests.log: ../test.pl

else
test:
	-@ln -s goto-cc ../../src/goto-cc/goto-gcc
	@../test.pl -p -c ../../../src/goto-cc/goto-gcc

tests.log: ../test.pl
	-@ln -s goto-cc ../../src/goto-cc/goto-gcc
	@../test.pl -p -c ../../../src/goto-cc/goto-gcc

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
	find -name '*.goto-cc-saved' -execdir $(RM) '{}' \;
	$(RM) tests.log
