default: tests.log

include ../../src/config.inc
include ../../src/common

ifeq ($(BUILD_ENV_),MSVC)
	exe = ../../../src/goto-cc/goto-cl
else
	exe = ../../../src/goto-cc/goto-cc
endif

ifeq ($(BUILD_ENV_),MSVC)
	excluded_tests = -X gcc-only
else
ifeq ($(BUILD_ENV_),OSX)
	# In MacOS, a change in the assert.h header file
	# is causing template errors when exercising the
	# C++ front end (because of a transitive include
	# of <type_traits>) for files that include the
	# <assert.h> or <cassert> headers.
  excluded_tests = -X macos-assert-broken
endif
endif

test:
	if which clang ; then \
	  ../test.pl -e -p -c "$(exe) --native-compiler clang" $(excluded_tests) ; \
	fi
	if which gcc ; then \
	  ../test.pl -e -p -c "$(exe) --native-compiler gcc" $(excluded_tests) -X fake-gcc-version && \
	  ../test.pl -e -p -c $(exe) $(excluded_tests) -I fake-gcc-version ; \
	elif ! which clang ; then \
	  ../test.pl -e -p -c $(exe) $(excluded_tests) ; \
	fi
ifneq ($(BUILD_ENV_),MSVC)
	@../test.pl -e -p -c "$(exe) -xc++ -D_Bool=bool" -I test-c++-front-end -s c++-front-end $(excluded_tests)
endif

tests.log: ../test.pl
	if which clang ; then \
	  ../test.pl -e -p -c "$(exe) --native-compiler clang" $(excluded_tests) ; \
	fi
	if which gcc ; then \
	  ../test.pl -e -p -c "$(exe) --native-compiler gcc" $(excluded_tests) -X fake-gcc-version && \
	  ../test.pl -e -p -c $(exe) $(excluded_tests) -I fake-gcc-version ; \
	elif ! which clang ; then \
	  ../test.pl -e -p -c $(exe) $(excluded_tests) ; \
	fi
ifneq ($(BUILD_ENV_),MSVC)
	@../test.pl -e -p -c "$(exe) -xc++ -D_Bool=bool" -I test-c++-front-end -s c++-front-end $(excluded_tests)
endif

clean:
	find . -name '*.out' -execdir $(RM) '{}' \;
	find . -name '*.gb' -execdir $(RM) '{}' \;
	$(RM) tests.log tests-c++-front-end.log
