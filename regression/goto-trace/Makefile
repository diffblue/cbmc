default: tests.log

test:
	@if ! ../test.pl -c python; then \
		../failed-tests-printer.pl ; \
		exit 1 ; \
	fi

tests.log: ../../lib/cbmc/regression/test.pl
	@if ! ../../lib/cbmc/regression/test.pl -c ../../../src/test-generator/test-generator ; then \
		../failed-tests-printer.pl ; \
		exit 1 ; \
	fi

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.java" "$$dir/*.out"; \
		fi; \
	done;
