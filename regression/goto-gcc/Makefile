default: tests.log

include ../../src/config.inc
include ../../src/common

ifeq ($(BUILD_ENV_),MSVC)
test:

tests.log: ../test.pl

else
test: ../../src/goto-cc/goto-gcc
	@../test.pl -e -p -c ../../../src/goto-cc/goto-gcc

tests.log: ../test.pl ../../src/goto-cc/goto-gcc
	@../test.pl -e -p -c ../../../src/goto-cc/goto-gcc

../../src/goto-cc/goto-gcc: ../../src/goto-cc/goto-cc
	@ln -sf goto-cc ../../src/goto-cc/goto-gcc

test tests.log: archives/libour_archive.a
archives/libour_archive.a: archives/foo.c ../../src/goto-cc/goto-gcc
	@cd archives && \
		../../../src/goto-cc/goto-gcc -c foo.c && \
		$(AR) rcs libour_archive.a foo.o
endif

show:
	@for dir in *; do \
	  if [ -d "$$dir" ]; then \
	    vim -o "$$dir/*.c" "$$dir/*.out"; \
	  fi; \
	done;

clean:
	find -name '*.out' -execdir $(RM) '{}' \;
	find -name '*.gb' -execdir $(RM) '{}' \;
	find -name '*.goto-cc-saved' -execdir $(RM) '{}' \;
	$(RM) tests.log archives/lib_ourarchive.a archives/foo.o
