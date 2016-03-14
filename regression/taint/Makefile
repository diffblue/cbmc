default: tests.log

test:
	@../test.pl -c ../../../src/goto-analyser/goto-analyser

tests.log: ../test.pl
	@../test.pl -c ../../../src/goto-analyser/goto-analyser

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.java" "$$dir/*.out"; \
		fi; \
	done;
