default: tests.log

test:
	@../test.pl -c "../../../src/cbmc/cbmc --unwind 2"

tests.log: ../test.pl
	@../test.pl -c "../../../src/cbmc/cbmc --unwind 2"

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.c" "$$dir/*.out"; \
		fi; \
	done;

clean:
	@rm -f */*.out