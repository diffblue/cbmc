
DIRS = ansi-c cbmc cpp goto-instrument goto-analyzer cbmc-java \
       goto-cc-goto-analyzer \
       goto-cc-symex \
       # Empty last line

test:
	$(foreach var,$(DIRS), $(MAKE) -C $(var) test || exit 1;)
