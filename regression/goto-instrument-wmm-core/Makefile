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

testalpha:
	@../test.pl -C -e -p -c '../chain.sh $(exe) ../../../src/goto-instrument/goto-instrument ../../../src/cbmc/cbmc $(is_windows)' -X glpk

testbeta:
	@../test.pl -T -e -p -c '../chain.sh $(exe) ../../../src/goto-instrument/goto-instrument ../../../src/cbmc/cbmc $(is_windows)' -X glpk

testimpr:
	@../test.pl -K -e -p -c '../chain.sh $(exe) ../../../src/goto-instrument/goto-instrument ../../../src/cbmc/cbmc $(is_windows)' -X glpk

testnew:
	@../test.pl -F -e -p -c '../chain.sh $(exe) ../../../src/goto-instrument/goto-instrument ../../../src/cbmc/cbmc $(is_windows)' -X glpk

test:
	@../test.pl -e -p -c '../chain.sh $(exe) ../../../src/goto-instrument/goto-instrument ../../../src/cbmc/cbmc $(is_windows)' -X glpk

tests.log:
	@../test.pl -e -p -c '../chain.sh $(exe) ../../../src/goto-instrument/goto-instrument ../../../src/cbmc/cbmc $(is_windows)' -X glpk

clean:
	find . -name '*.out' -execdir $(RM) '{}' \;
	find . -name '*.gb' -execdir $(RM) '{}' \;
	find . -name '*.dot' -execdir $(RM) '{}' \;
	find . -mindepth 2 -name '*.txt' -execdir $(RM) '{}' \;
	$(RM) tests.log
