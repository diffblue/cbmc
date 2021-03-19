default: tests.log

include ../../src/config.inc
include ../../src/common

ifeq ($(BUILD_ENV_),MSVC)
test:

tests.log: ../test.pl

else
test: ../../src/goto-cc/goto-ld
	@../test.pl -e -p -c ../../../src/goto-cc/goto-ld

tests.log: ../test.pl ../../src/goto-cc/goto-ld
	@../test.pl -e -p -c ../../../src/goto-cc/goto-ld

../../src/goto-cc/goto-ld: ../../src/goto-cc/goto-cc
	@ln -sf goto-cc ../../src/goto-cc/goto-ld
endif

clean:
	find . -name '*.out' -execdir $(RM) '{}' \;
	find . -name '*.gb' -execdir $(RM) '{}' \;
	find . -name '*.goto-cc-saved' -execdir $(RM) '{}' \;
	$(RM) tests.log
