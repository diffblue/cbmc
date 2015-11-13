DIRS = array-refinement array-refinement-with-incr \
       cbmc cbmc-with-incr \
       cbmc-incr cbmc-incr-oneloop 

test:
	$(foreach var,$(DIRS), make -C $(var) test;)

clean:
	$(foreach var,$(DIRS), make -C $(var) clean;)
