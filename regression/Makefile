
DIRS = ansi-c cbmc cpp goto-instrument goto-analyzer

test:
	$(foreach var,$(DIRS), $(MAKE) -C $(var) test || exit 1;)
