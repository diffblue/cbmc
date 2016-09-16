default: tests.log

PARAM = --incremental 
# --refine   --slice-formula

test:
	@../test.pl -c "perl -e 'alarm shift @ARGV; exec @ARGV' 30 ../../../src/cbmc/cbmc $(PARAM)"

tests.log: ../test.pl
	@../test.pl -c "perl -e 'alarm shift @ARGV; exec @ARGV' 30 ../../../src/cbmc/cbmc $(PARAM)"

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.c" "$$dir/*.out"; \
		fi; \
	done;

clean:
	@$(RM) *.log
	@(for dir in *; do $(RM) $$dir/*.out; done;)
