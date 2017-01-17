
DIRS = ansi-c cbmc cpp goto-instrument goto-instrument-unwind goto-analyzer inlining

test:
	$(foreach var,$(DIRS), $(MAKE) -C $(var) test || exit 1;)
