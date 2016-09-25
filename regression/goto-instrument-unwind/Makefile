default: tests.log

testalpha:
	@../test.pl -c ../unwind-chain.sh -C

testbeta:
	@../test.pl -c ../unwind-chain.sh -T

testimpr:
	@../test.pl -c ../unwind-chain.sh -K

testnew:
	@../test.pl -c ../unwind-chain.sh -F

test:
	@../test.pl -c ../unwind-chain.sh

tests.log: ../test.pl
	@../test.pl -c ../unwind-chain.sh

clean:
	@for dir in *; do \
                if [ -d "$$dir" ]; then \
                        rm -f $$dir/*.txt $$dir/*.dot $$dir/*.gb $$dir/*.out; \
                fi; \
  done;
	rm -f tests.log

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.c" "$$dir/*.out"; \
		fi; \
	done;
