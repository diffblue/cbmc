default: tests.log

TIMEOUT = 900
UNWIND = 3

test:
	@echo $(UNWIND) unwindings
	@../test.pl -c "time perl -e 'alarm shift @ARGV; exec @ARGV' $(TIMEOUT) ../../../src/cbmc/cbmc --unwind $(UNWIND)"

tests.log: ../test.pl
	@../test.pl -c "time perl -e 'alarm shift @ARGV; exec @ARGV' $(TIMEOUT) ../../../src/cbmc/cbmc --unwind $(UNWIND)"

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.c" "$$dir/*.out"; \
		fi; \
	done;

clean:
	@rm -f */*.out tests.log