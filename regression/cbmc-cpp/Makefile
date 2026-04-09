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

# Exclude libc++ tests when libc++ headers are not installed
ifeq ($(wildcard /usr/include/c++/v1/vector),)
  ifeq ($(wildcard /Library/Developer/CommandLineTools/SDKs/*/usr/include/c++/v1/vector),)
    excluded_libcxx = -X libcxx
  endif
endif

test:
	@../test.pl -e -p -c "../../../src/cbmc/cbmc --validate-goto-model --validate-ssa-equation" $(excluded_tests) $(excluded_libcxx) -X libcxx-slow -t 1800

tests.log: ../test.pl
	@../test.pl -e -p -c "../../../src/cbmc/cbmc --validate-goto-model --validate-ssa-equation" $(excluded_tests) $(excluded_libcxx) -X libcxx-slow -t 1800

clean:
	find . -name '*.out' -execdir $(RM) '{}' \;
	find . -name '*.gb' -execdir $(RM) '{}' \;
	$(RM) tests.log
