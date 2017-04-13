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
	@$(RM) *.log
	@for dir in *; do $(RM) $$dir/*.out; done;
