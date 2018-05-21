default: tests.log

include ../../src/config.inc

test:
	@../$(CPROVER_DIR)/regression/test.pl -p -c ../../../src/jbmc/jbmc
	@../$(CPROVER_DIR)/regression/test.pl -p -c "../../../src/jbmc/jbmc --symex-driven-lazy-loading" -X symex-driven-lazy-loading-expected-failure

testfuture:
	@../$(CPROVER_DIR)/regression/test.pl -p -c ../../../src/jbmc/jbmc -CF
	@../$(CPROVER_DIR)/regression/test.pl -p -c "../../../src/jbmc/jbmc --symex-driven-lazy-loading" -X symex-driven-lazy-loading-expected-failure -CF

testall:
	@../$(CPROVER_DIR)/regression/test.pl -p -c ../../../src/jbmc/jbmc -CFTK
	@../$(CPROVER_DIR)/regression/test.pl -p -c "../../../src/jbmc/jbmc --symex-driven-lazy-loading" -X symex-driven-lazy-loading-expected-failure -CFTK

tests.log: ../$(CPROVER_DIR)/regression/test.pl
	@../$(CPROVER_DIR)/regression/test.pl -p -c ../../../src/jbmc/jbmc
	@../$(CPROVER_DIR)/regression/test.pl -p -c "../../../src/jbmc/jbmc --symex-driven-lazy-loading" -X symex-driven-lazy-loading-expected-failure

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

