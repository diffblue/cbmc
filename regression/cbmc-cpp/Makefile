default: tests.log

test:
	@../test.pl -c ../../../src/cbmc/cbmc

tests.log: ../test.pl
	@../test.pl -c ../../../src/cbmc/cbmc

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.c" "$$dir/*.out"; \
		fi; \
	done;
