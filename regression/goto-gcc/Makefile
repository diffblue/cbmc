default: tests.log

include ../../src/config.inc
include ../../src/common

ifeq ($(BUILD_ENV_),MSVC)
test:

tests.log: ../test.pl

else
ifeq ($(BUILD_ENV_),OSX)
  not_gnu_ld = -X gnu-ld-only
endif
test: ../../src/goto-cc/goto-gcc
	@PATH=../../../scripts:$$PATH \
		../test.pl -e -p -c ../../../src/goto-cc/goto-gcc $(not_gnu_ld)

tests.log: ../test.pl ../../src/goto-cc/goto-gcc
	@PATH=../../../scripts:$$PATH \
		../test.pl -e -p -c ../../../src/goto-cc/goto-gcc $(not_gnu_ld)

../../src/goto-cc/goto-gcc: ../../src/goto-cc/goto-cc
	@ln -sf goto-cc ../../src/goto-cc/goto-gcc

../../src/goto-cc/goto-ld: ../../src/goto-cc/goto-cc
	@ln -sf goto-cc ../../src/goto-cc/goto-ld

test tests.log: archives/libour_archive.a
archives/libour_archive.a: archives/foo.c ../../src/goto-cc/goto-gcc
	@cd archives && \
		../../../src/goto-cc/goto-gcc -c foo.c && \
		$(AR) rcs libour_archive.a foo.o
endif

clean:
	find . -name '*.out' -execdir $(RM) '{}' \;
	find . -name '*.gb' -execdir $(RM) '{}' \;
	find . -name '*.goto-cc-saved' -execdir $(RM) '{}' \;
	$(RM) tests.log archives/libour_archive.a archives/foo.o
