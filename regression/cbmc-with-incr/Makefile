default: tests.log

test:
	@../test.pl -c "../../../src/cbmc/cbmc --no-standard-checks --incremental"

tests.log: ../test.pl
	@../test.pl -c "../../../src/cbmc/cbmc --no-standard-checks --incremental"

clean:
	@$(RM) *.log
	@for dir in *; do $(RM) $$dir/*.out; done;
