default: tests.log

include ../../src/config.inc
include ../../src/common

ifeq ($(filter-out OSX MSVC FreeBSD,$(BUILD_ENV_)),)
	# no POSIX threads on Windows
	# for OSX and FreeBSD we'd need sound handling of pointers in multi-threaded programs
	no_pthread = -X pthread
endif

ifeq ($(BUILD_ENV_),MSVC)
	gcc_only = -X gcc-only
endif

test:
	@../test.pl -e -p -c "../../../src/cbmc/cbmc --validate-goto-model --validate-ssa-equation" $(no_pthread) $(gcc_only)

tests.log: ../test.pl
	@../test.pl -e -p -c "../../../src/cbmc/cbmc --validate-goto-model --validate-ssa-equation" $(no_pthread) $(gcc_only)

clean:
	find . -name '*.out' -execdir $(RM) '{}' \;
	find . -name '*.gb' -execdir $(RM) '{}' \;
	$(RM) tests.log
