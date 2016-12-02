DIRS = ansi-c cbmc cpp goto-instrument

test:
	$(foreach var,$(DIRS), $(MAKE) -C $(var) test || exit 1;)
