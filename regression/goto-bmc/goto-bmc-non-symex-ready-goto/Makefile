default: tests.log

include ../../../src/config.inc
include ../../../src/common

GOTO_BMC_EXE=../../../../src/goto-bmc/goto-bmc

ifeq ($(BUILD_ENV_),MSVC)
	GOTO_CC_EXE=../../../../src/goto-cc/goto-cl
	is_windows=true
else
	GOTO_CC_EXE=../../../../src/goto-cc/goto-cc
	is_windows=false
endif

test:
	@../../test.pl -e -p -c "../chain.sh $(GOTO_CC_EXE) $(GOTO_BMC_EXE) $(is_windows)"

tests.log: ../test.pl
	@../../test.pl -e -p -c "../chain.sh $(GOTO_CC_EXE) $(GOTO_BMC_EXE) $(is_windows)"

clean:
	find . -name '*.out' -execdir $(RM) '{}' \;
	find . -name '*.gb' -execdir $(RM) {} \;
	$(RM) tests.log
