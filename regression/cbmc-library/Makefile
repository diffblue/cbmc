default: tests.log

include ../../src/config.inc
include ../../src/common

ifeq ($(BUILD_ENV_),MSVC)
	unix_only = -X unix
	gcc_only = -X gcc-only
endif

# `x86-preprocessing': the test preprocesses for an x86 target (--winx64:
# gcc -m64), which GNU gcc for another architecture (aarch64) rejects
ifneq ($(BUILD_ENV_),MSVC)
  ifneq ($(shell uname -s),Darwin)
    ifeq ($(filter x86_64 amd64 i386 i486 i586 i686,$(shell uname -m)),)
      gcc_only += -X x86-preprocessing
    endif
  endif
endif

test:
	@../test.pl -e -p -c ../../../src/cbmc/cbmc $(unix_only) $(gcc_only)

tests.log: ../test.pl
	@../test.pl -e -p -c ../../../src/cbmc/cbmc $(unix_only) $(gcc_only)

clean:
	find . -name '*.out' -execdir $(RM) '{}' \;
	$(RM) tests.log
