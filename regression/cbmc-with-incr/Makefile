default: tests.log

test:
	@../test.pl -c "../../../src/cbmc/cbmc --incremental"

tests.log: ../test.pl
	@../test.pl -c "../../../src/cbmc/cbmc --incremental"

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.c" "$$dir/*.out"; \
		fi; \
	done;

clean:
	@rm -f *.log
	@for dir in *; do rm -f $$dir/*.out; done;
