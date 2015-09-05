default: tests.log

test:
	@../test.pl -c ../../../src/goto-instrument/accelerate/accelerate.sh

tests.log: ../test.pl
	@../test.pl -c ../../../src/goto-instrument/accelerate/accelerate.sh

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.c" "$$dir/*.out"; \
		fi; \
	done;

clean:
	rm -f tests.log
	rm -f */main.out
