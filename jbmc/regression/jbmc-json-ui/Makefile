default: tests.log

include ../../src/config.inc

test:
ifeq (, $(shell which jq))
	echo "JBMC JSON-UI tests skipped (can't find 'jq' in your path)"
else
	@../$(CPROVER_DIR)/regression/test.pl -p -c "../chain.sh ../../../src/jbmc/jbmc"
endif

tests.log: ../$(CPROVER_DIR)/regression/test.pl test

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.java" "$$dir/*.out"; \
		fi; \
	done;

clean:
	find -name '*.out' -execdir $(RM) '{}' \;
	find -name '*.gb' -execdir $(RM) '{}' \;
	$(RM) tests.log tests-symex-driven-loading.log

%.class: %.java ../../src/org.cprover.jar
	javac -g -cp ../../src/org.cprover.jar:. $<

nondet_java_files := $(shell find . -name "Nondet*.java")
nondet_class_files := $(patsubst %.java, %.class, $(nondet_java_files))

.PHONY: nondet-class-files
nondet-class-files: $(nondet_class_files)

.PHONY: clean-nondet-class-files
clean-nondet-class-files:
	-rm $(nondet_class_files)
