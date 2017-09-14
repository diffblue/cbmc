default: tests.log

test:
	@if ! ../test.pl -c ../chain.sh ; then \
		../failed-tests-printer.pl ; \
		exit 1; \
	fi

tests.log:
	@if ! ../test.pl -c ../chain.sh ; then \
		../failed-tests-printer.pl ; \
		exit 1; \
	fi

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.c" "$$dir/*.out"; \
		fi; \
	done;

clean:
	@for dir in *; do \
		$(RM) tests.log; \
		if [ -d "$$dir" ]; then \
			cd "$$dir"; \
			$(RM) *.out *.gb; \
			cd ..; \
		fi \
	done
