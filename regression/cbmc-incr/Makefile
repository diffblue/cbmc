default: tests.log

PARAM = --incremental --magic-numbers
# --refine   --slice-formula

test:
	@../test.pl -c "perl -e 'alarm shift @ARGV; exec @ARGV' 30 ../../../src/cbmc/cbmc $(PARAM)"

tests.log: ../test.pl
	@../test.pl -c "perl -e 'alarm shift @ARGV; exec @ARGV' 30 ../../../src/cbmc/cbmc $(PARAM)"

clean:
	@$(RM) *.log
	@(for dir in *; do $(RM) $$dir/*.out; done;)
