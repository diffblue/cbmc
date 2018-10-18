default: tests.log

test:
	@../test.pl -p -c ../../../src/cbmc/cbmc

tests.log: ../test.pl
	@../test.pl -p -c ../../../src/cbmc/cbmc

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.c" "$$dir/*.out"; \
		fi; \
	done;

clean:
	find -name '*.out' -execdir $(RM) '{}' \;
	$(RM) tests.log
