DIRS = cbmc cbmc-incr cbmc-incr-oneloop cbmc-with-incr

test:
	$(foreach var,$(DIRS), make -C $(var) test;)

clean:
	$(foreach var,$(DIRS), make -C $(var) clean;)
