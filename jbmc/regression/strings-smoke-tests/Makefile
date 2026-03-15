default: tests.log

include ../../src/config.inc

test:
ifndef ONLY_SYMEX_DRIVEN_LAZY_LOADING
	@../$(CPROVER_DIR)/regression/test.pl -e -p -c "../../../src/jbmc/jbmc --validate-goto-model --validate-ssa-equation"
endif
ifndef SKIP_SYMEX_DRIVEN_LAZY_LOADING
	@../$(CPROVER_DIR)/regression/test.pl -e -p -c "../../../src/jbmc/jbmc --validate-goto-model --validate-ssa-equation --symex-driven-lazy-loading" -X symex-driven-lazy-loading-expected-failure -s symex-driven-loading
endif

testfuture:
	@../$(CPROVER_DIR)/regression/test.pl -e -p -c "../../../src/jbmc/jbmc --validate-goto-model --validate-ssa-equation" -CF
ifndef SKIP_SYMEX_DRIVEN_LAZY_LOADING
	@../$(CPROVER_DIR)/regression/test.pl -e -p -c "../../../src/jbmc/jbmc --validate-goto-model --validate-ssa-equation --symex-driven-lazy-loading" -X symex-driven-lazy-loading-expected-failure -CF -s symex-driven-loading
endif

testall:
	@../$(CPROVER_DIR)/regression/test.pl -e -p -c "../../../src/jbmc/jbmc --validate-goto-model --validate-ssa-equation" -CFTK
ifndef SKIP_SYMEX_DRIVEN_LAZY_LOADING
	@../$(CPROVER_DIR)/regression/test.pl -e -p -c "../../../src/jbmc/jbmc --validate-goto-model --validate-ssa-equation --symex-driven-lazy-loading" -X symex-driven-lazy-loading-expected-failure -CFTK -s symex-driven-loading
endif

tests.log: ../$(CPROVER_DIR)/regression/test.pl
ifndef ONLY_SYMEX_DRIVEN_LAZY_LOADING
	@../$(CPROVER_DIR)/regression/test.pl -e -p -c "../../../src/jbmc/jbmc --validate-goto-model --validate-ssa-equation"
endif
ifndef SKIP_SYMEX_DRIVEN_LAZY_LOADING
	@../$(CPROVER_DIR)/regression/test.pl -e -p -c "../../../src/jbmc/jbmc --validate-goto-model --validate-ssa-equation --symex-driven-lazy-loading" -X symex-driven-lazy-loading-expected-failure -s symex-driven-loading
endif

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
