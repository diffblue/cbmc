default: tests.log

testalpha:
	@../test.pl -c ../chain.sh -C

testbeta:
	@../test.pl -c ../chain.sh -T

testimpr:
	@../test.pl -c ../chain.sh -K

testnew:
	@../test.pl -c ../chain.sh -F

test:
	@../test.pl -c ../chain.sh 

tests.log: ../test.pl
	@../test.pl -c ../chain.sh 

clean:
	@for dir in *; do \
                if [ -d "$$dir" ]; then \
                        rm $$dir/*.txt $$dir/*.dot $$dir/*.gb $$dir/*.out; \
                fi; \
        done;

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.c" "$$dir/*.out"; \
		fi; \
	done;
