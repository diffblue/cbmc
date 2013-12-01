DIRS = cbmc-incr cbmc-incr-bounds

test:
	$(foreach var,$(DIRS), make -C $(var) test;)

clean:
	$(foreach var,$(DIRS), make -C $(var) clean;)
