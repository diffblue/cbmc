DIRS = cbmc-incr cbmc-with-incr cbmc-from-CVS-with-incr

test:
	$(foreach var,$(DIRS), make -C $(var) test;)

clean:
	$(foreach var,$(DIRS), make -C $(var) clean;)
