default: tests.log

test:
	@../test.pl -p -c ../../../src/jbmc/jbmc

testfuture:
	@../test.pl -p -c ../../../src/jbmc/jbmc -CF

testall:
	@../test.pl -p -c ../../../src/jbmc/jbmc -CFTK

tests.log: ../test.pl
	@../test.pl -p -c ../../../src/jbmc/jbmc

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

