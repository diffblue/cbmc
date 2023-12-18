default: tests.log

SRC = call_bmc.cpp

OBJ += ../../src/libcprover-cpp/libcprover-cpp$(LIBEXT)

INCLUDES = -I ../../src/ -I ../../src/goto-programs/

CLEANFILES = api-binary-driver$(EXEEXT)

include ../../src/config.inc
include ../../src/common

api-binary-driver$(EXEEXT): $(OBJ)
	$(LINKBIN)

DIRS = \
  model_loading

test:
	@for dir in $(DIRS); do \
		$(MAKE) -C "$$dir" test || exit 1; \
	done;

tests.log:
	@for dir in $(DIRS); do \
		$(MAKE) -C "$$dir" tests.log || exit 1; \
	done;

test tests.log: api-binary-driver$(EXEEXT)

clean: regression_clean

.PHONY: regression_clean
regression_clean:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			$(MAKE) -C "$$dir" clean; \
		fi; \
	done;
	$(RM) tests.log
