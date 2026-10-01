default: tests.log

include ../../src/config.inc
include ../../src/common

ifeq ($(BUILD_ENV_),MSVC)
  excluded_tests = -X gcc-only
else ifneq ($(shell ../../../src/goto-cc/goto-cc --version 2>&1 | grep -c 'gcc:'),0)
  excluded_tests =
else
  excluded_tests = -X gcc-only
endif

# Tests tagged `libstdcxxNN' need the libstdc++ headers of GCC >= NN (cbmc
# preprocesses with the host gcc); exclude those the host cannot provide.
host_gcc_major = $(shell gcc -dumpversion 2>/dev/null | cut -d. -f1)
ifeq ($(shell test -n "$(host_gcc_major)" && test $(host_gcc_major) -ge 12 && echo yes),yes)
  excluded_libstdcxx =
else
  excluded_libstdcxx = -X libstdcxx12
endif
ifneq ($(shell test -n "$(host_gcc_major)" && test $(host_gcc_major) -ge 16 && echo yes),yes)
  excluded_libstdcxx += -X libstdcxx16
else
  # known to fail with the libstdc++ 16 headers (temporary, see README)
  excluded_libstdcxx += -X broken-libstdcxx16
endif

# Exclude libc++ tests when libc++ headers are not installed
ifeq ($(wildcard /usr/include/c++/v1/vector),)
  ifeq ($(wildcard /Library/Developer/CommandLineTools/SDKs/*/usr/include/c++/v1/vector),)
    excluded_libcxx = -X libcxx
  endif
endif

test:
	@../test.pl -e -p -c "../../../src/cbmc/cbmc --validate-goto-model --validate-ssa-equation" $(excluded_tests) $(excluded_libstdcxx) $(excluded_libcxx) -t 1800

tests.log: ../test.pl
	@../test.pl -e -p -c "../../../src/cbmc/cbmc --validate-goto-model --validate-ssa-equation" $(excluded_tests) $(excluded_libstdcxx) $(excluded_libcxx) -t 1800

clean:
	find . -name '*.out' -execdir $(RM) '{}' \;
	find . -name '*.gb' -execdir $(RM) '{}' \;
	$(RM) tests.log
