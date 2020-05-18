include ../../src/config.inc
include ../../src/common

ifeq ($(BUILD_ENV_),MSVC)
	exe=../../../src/goto-cc/goto-cl
	is_windows=true
else
	exe=../../../src/goto-cc/goto-cc
	is_windows=false
endif

test:
	@../test.pl -e -p -c '../chain.sh \
	   ../../../src/goto-analyzer/goto-analyzer \
	   $(exe) \
	   ../../../src/goto-instrument/goto-instrument \
	   ../../../src/cbmc/cbmc \
	   ${is_windows}'
