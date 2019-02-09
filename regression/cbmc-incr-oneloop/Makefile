default: tests.log

test:
	@../test.pl -c "perl -e 'alarm shift @ARGV; exec @ARGV' 8 ../../../src/cbmc/cbmc --slice-formula"

tests.log: ../test.pl
	@../test.pl -c "perl -e 'alarm shift @ARGV; exec @ARGV' 8 ../../../src/cbmc/cbmc --slice-formula"

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.c" "$$dir/*.out"; \
		fi; \
	done;

clean:
	@$(RM) *.log
	@(for dir in *; do $(RM) $$dir/*.out; done;)
