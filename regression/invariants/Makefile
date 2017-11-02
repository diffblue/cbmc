default: tests.log

SRC = driver.cpp

INCLUDES = -I ../../src

OBJ += ../../src/big-int/big-int$(LIBEXT) \
      ../../src/util/util$(LIBEXT)

include ../../src/config.inc
include ../../src/common

test: driver$(EXEEXT)
	@../test.pl -p -c ../driver

tests.log: ../test.pl driver$(EXEEXT)
	@../test.pl -p -c ../driver

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.c" "$$dir/*.out"; \
		fi; \
	done;

driver$(EXEEXT): $(OBJ)
	$(LINKBIN)
