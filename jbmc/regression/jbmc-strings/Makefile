default: tests.log

include ../../src/config.inc

# SHARD restricts the long-running symex-driven-lazy-loading run to a single
# shard "<index>/<count>" (see test.pl --shard); the parent Makefile sets it to
# spread this profile across parallel workers. An empty SHARD runs the whole
# profile. Each shard writes a distinct log so concurrent shards do not clobber
# one another.
SHARD =
symex_driven_log = symex-driven-loading$(if $(SHARD),-$(firstword $(subst /, ,$(SHARD))))
symex_driven_opts = -X symex-driven-lazy-loading-expected-failure $(if $(SHARD),--shard $(SHARD)) -s $(symex_driven_log)

.PHONY: test test-normal test-symex-driven-lazy-loading
test: test-normal test-symex-driven-lazy-loading

test-normal:
	@../$(CPROVER_DIR)/regression/test.pl -e -p -c "../../../src/jbmc/jbmc --validate-goto-model --validate-ssa-equation"

test-symex-driven-lazy-loading:
	@../$(CPROVER_DIR)/regression/test.pl -e -p -c "../../../src/jbmc/jbmc --validate-goto-model --validate-ssa-equation --symex-driven-lazy-loading" $(symex_driven_opts)

testfuture:
	@../$(CPROVER_DIR)/regression/test.pl -e -p -c "../../../src/jbmc/jbmc --validate-goto-model --validate-ssa-equation" -CF
	@../$(CPROVER_DIR)/regression/test.pl -e -p -c "../../../src/jbmc/jbmc --validate-goto-model --validate-ssa-equation --symex-driven-lazy-loading" -X symex-driven-lazy-loading-expected-failure -CF -s symex-driven-loading

testall:
	@../$(CPROVER_DIR)/regression/test.pl -e -p -c "../../../src/jbmc/jbmc --validate-goto-model --validate-ssa-equation" -CFTK
	@../$(CPROVER_DIR)/regression/test.pl -e -p -c "../../../src/jbmc/jbmc --validate-goto-model --validate-ssa-equation --symex-driven-lazy-loading" -X symex-driven-lazy-loading-expected-failure -CFTK -s symex-driven-loading

tests.log: ../$(CPROVER_DIR)/regression/test.pl
	@../$(CPROVER_DIR)/regression/test.pl -e -p -c "../../../src/jbmc/jbmc --validate-goto-model --validate-ssa-equation"
	@../$(CPROVER_DIR)/regression/test.pl -e -p -c "../../../src/jbmc/jbmc --validate-goto-model --validate-ssa-equation --symex-driven-lazy-loading" -X symex-driven-lazy-loading-expected-failure -s symex-driven-loading

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.c" "$$dir/*.out"; \
		fi; \
	done;

clean:
	find -name '*.out' -execdir $(RM) '{}' \;
	find -name '*.gb' -execdir $(RM) '{}' \;
	$(RM) tests.log tests-symex-driven-loading*.log
