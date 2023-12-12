default: tests.log

# Note the `perl -e` serves the purpose of providing timeout
test:
	@../test.pl -c "perl -e 'alarm shift @ARGV; exec @ARGV' 15 ../../../src/cbmc/cbmc --slice-formula"

tests.log: ../test.pl
	@../test.pl -c "perl -e 'alarm shift @ARGV; exec @ARGV' 15 ../../../src/cbmc/cbmc --slice-formula"

clean:
	@$(RM) *.log
	@(for dir in *; do $(RM) $$dir/*.out; done;)
