default: tests.log

GOTO_HARNESS_EXE=../../../src/goto-harness/goto-harness

test:
	@../test.pl -p -c ${GOTO_HARNESS_EXE}

tests.log: ../test.pl
	@../test.pl -p -c ${GOTO_HARNESS_EXE}

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.c" "$$dir/*.out"; \
		fi; \
	done;

clean:
	find -name '*.out' -execdir $(RM) '{}' \;
	find -name '*.gb' -execdir $(RM) {} \;
	$(RM) tests.log
