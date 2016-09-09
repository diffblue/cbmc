default: tests.log

test:
	@if ! ../test.pl -c ../../../src/goto-analyzer/goto-analyzer ; then \
		../failed-tests-printer.pl ; \
		exit 1 ; \
	fi

tests.log: ../test.pl
	@if ! ../test.pl -c ../../../src/goto-analyzer/goto-analyzer ; then \
		../failed-tests-printer.pl ; \
		exit 1 ; \
	fi

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.java" "$$dir/*.out"; \
		fi; \
	done;

clean:
	find . -name *.*~ | xargs rm -f
	find . -name *.out | xargs rm -f
	find . -name *.goto | xargs rm -f
	rm -f tests.log	
