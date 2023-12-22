default: tests.log

test:
	@../test.pl -c "../../../src/cbmc/cbmc --incremental"

tests.log: ../test.pl
	@../test.pl -c "../../../src/cbmc/cbmc --incremental"

clean:
	@$(RM) *.log
	@for dir in *; do $(RM) $$dir/*.out; done;
