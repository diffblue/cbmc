DIRS = ansi-c cbmc cpp goto-instrument goto-instrument-unwind

test:
	$(foreach var,$(DIRS), $(MAKE) -C $(var) test || exit 1;)
