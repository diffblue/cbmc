default: tests.log

test:
	@../test.pl -e -p -c ../../../src/goto-diff/goto-diff

tests.log: ../test.pl
	@../test.pl -e -p -c ../../../src/goto-diff/goto-diff

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.c" "$$dir/*.out"; \
		fi; \
	done;

clean:
	find -name '*.out' -execdir $(RM) '{}' \;
	$(RM) tests.log
