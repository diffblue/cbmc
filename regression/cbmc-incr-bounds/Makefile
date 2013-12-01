default: tests.log

test:
	@../test.pl -c "perl -e 'alarm shift @ARGV; exec @ARGV' 3 ../../../src/cbmc/cbmc --incremental-check c::main.0 --no-unwinding-assertions --unwind 10"

tests.log: ../test.pl
	@../test.pl -c "perl -e 'alarm shift @ARGV; exec @ARGV' 3 ../../../src/cbmc/cbmc --incremental-check c::main.0 --no-unwinding-assertions --unwind 10"

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.c" "$$dir/*.out"; \
		fi; \
	done;

clean:
	@rm -f *.out
	@for dir in *; do rm -f $$dir/*.out; done;
