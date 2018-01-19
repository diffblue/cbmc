default: tests.log

test:
	@../test.pl -p -c ../../../src/jbmc/jbmc
	@../test.pl -p -c "../../../src/jbmc/jbmc --symex-driven-lazy-loading" -X symex-driven-lazy-loading-expected-failure

testfuture:
	@../test.pl -p -c ../../../src/jbmc/jbmc -CF
	@../test.pl -p -c "../../../src/jbmc/jbmc --symex-driven-lazy-loading" -X symex-driven-lazy-loading-expected-failure -CF

testall:
	@../test.pl -p -c ../../../src/jbmc/jbmc -CFTK
	@../test.pl -p -c "../../../src/jbmc/jbmc --symex-driven-lazy-loading" -X symex-driven-lazy-loading-expected-failure -CFTK

tests.log: ../test.pl
	@../test.pl -p -c ../../../src/jbmc/jbmc
	@../test.pl -p -c "../../../src/jbmc/jbmc --symex-driven-lazy-loading" -X symex-driven-lazy-loading-expected-failure

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

