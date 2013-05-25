default: tests.log

test:
	@../test.pl -c ../../../src/goto-cc/goto-cc

tests.log: ../test.pl
	@../test.pl -c ../../../src/goto-cc/goto-cc

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.c" "$$dir/*.out"; \
		fi; \
	done;
