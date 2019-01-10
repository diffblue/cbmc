default: tests.log

include ../../src/config.inc

test:
	@../$(CPROVER_DIR)/regression/test.pl -p -c "../../../src/jbmc/jbmc --validate-goto-model"
	@../$(CPROVER_DIR)/regression/test.pl -p -c "../../../src/jbmc/jbmc --validate-goto-model --symex-driven-lazy-loading" -X symex-driven-lazy-loading-expected-failure -s symex-driven-loading

testfuture:
	@../$(CPROVER_DIR)/regression/test.pl -p -c "../../../src/jbmc/jbmc --validate-goto-model" -CF
	@../$(CPROVER_DIR)/regression/test.pl -p -c "../../../src/jbmc/jbmc --validate-goto-model --symex-driven-lazy-loading" -X symex-driven-lazy-loading-expected-failure -CF -s symex-driven-loading

testall:
	@../$(CPROVER_DIR)/regression/test.pl -p -c "../../../src/jbmc/jbmc --validate-goto-model" -CFTK
	@../$(CPROVER_DIR)/regression/test.pl -p -c "../../../src/jbmc/jbmc --validate-goto-model --symex-driven-lazy-loading" -X symex-driven-lazy-loading-expected-failure -CFTK -s symex-driven-loading

tests.log: ../$(CPROVER_DIR)/regression/test.pl
	@../$(CPROVER_DIR)/regression/test.pl -p -c "../../../src/jbmc/jbmc --validate-goto-model"
	@../$(CPROVER_DIR)/regression/test.pl -p -c "../../../src/jbmc/jbmc --validate-goto-model --symex-driven-lazy-loading" -X symex-driven-lazy-loading-expected-failure -s symex-driven-loading

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.c" "$$dir/*.out"; \
		fi; \
	done;

clean:
	find -name '*.out' -execdir $(RM) '{}' \;
	find -name '*.gb' -execdir $(RM) '{}' \;
	$(RM) tests.log tests-symex-driven-loading.log
