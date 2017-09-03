default: tests.log

SRC = driver.cpp

INCLUDES = -I ../../src

OBJ += ../../src/big-int/big-int$(LIBEXT) \
      ../../src/util/util$(LIBEXT)

include ../../src/config.inc
include ../../src/common

test: driver$(EXEEXT)
	@if ! ../test.pl -c ../driver ; then \
		../failed-tests-printer.pl ; \
		exit 1 ; \
	fi

tests.log: ../test.pl driver$(EXEEXT)
	@if ! ../test.pl -c ../driver ; then \
		../failed-tests-printer.pl ; \
		exit 1 ; \
	fi

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.c" "$$dir/*.out"; \
		fi; \
	done;

driver$(EXEEXT): $(OBJ)
	$(LINKBIN)
