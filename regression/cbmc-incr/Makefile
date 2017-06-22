default: tests.log

PARAM = --incremental 
# --refine   --slice-formula

test:
	@if ! ../test.pl -c "perl -e 'alarm shift @ARGV; exec @ARGV' 30 ../../../src/cbmc/cbmc --incremental" ; then \
	../failed-tests-printer.pl ; \
		exit 1 ; \
	fi

tests.log: ../test.pl
	@if ! ../test.pl -c "perl -e 'alarm shift @ARGV; exec @ARGV' 30 ../../../src/cbmc/cbmc --incremental" ; then \
	../failed-tests-printer.pl ; \

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.c" "$$dir/*.out"; \
		fi; \
	done;

clean:
	@$(RM) *.log
	@(for dir in *; do $(RM) $$dir/*.out; done;)
