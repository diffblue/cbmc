default: tests.log

test:
	@if ! ../test.pl -c ../../../src/cbmc/cbmc ; then \
		../failed-tests-printer.pl ; \
		exit 1 ; \
	fi

testfuture:
	@if ! ../test.pl -c ../../../src/cbmc/cbmc -CF ; then \
		../failed-tests-printer.pl ; \
		exit 1 ; \
	fi

testall:
	@if ! ../test.pl -c ../../../src/cbmc/cbmc -CFTK ; then \
		../failed-tests-printer.pl ; \
		exit 1 ; \
	fi

tests.log: ../test.pl
	@if ! ../test.pl -c ../../../src/cbmc/cbmc ; then \
		../failed-tests-printer.pl ; \
		exit 1 ; \
	fi

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.c" "$$dir/*.out"; \
		fi; \
	done;

clean:
	find -name '*.out' -execdir $(RM) '{}' \;
	find -name '*.gb' -execdir $(RM) '{}' \;
	$(RM) tests.log

