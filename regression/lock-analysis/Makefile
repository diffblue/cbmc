test:
	@./test.pl -c ../chain.sh 

clean:
	@for dir in *; do \
                if [ -d "$$dir" ]; then \
                        rm $$dir/*.xml $$dir/*.o $$dir/*.out; \
                fi; \
        done;
