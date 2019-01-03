default: tests.log

include ../../src/config.inc

test:
	@../$(CPROVER_DIR)/regression/test.pl -p -c ../../../src/janalyzer/janalyzer

tests.log: ../$(CPROVER_DIR)/regression/test.pl
	@../$(CPROVER_DIR)/regression/test.pl -p -c ../../../src/janalyzer/janalyzer

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.java" "$$dir/*.out"; \
		fi; \
	done;

clean:
	find -name '*.out' -execdir $(RM) '{}' \;
	find -name '*.gb' -execdir $(RM) '{}' \;
	$(RM) tests.log
