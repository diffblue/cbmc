default: tests.log

test:
	-@ln -s goto-cc ../../src/goto-cc/goto-gcc
	@if ! ../test.pl -c ../../../src/goto-cc/goto-gcc ; then \
	  ../failed-tests-printer.pl ; \
	  exit 1 ; \
	fi

tests.log: ../test.pl
	-@ln -s goto-cc ../../src/goto-cc/goto-gcc
	@if ! ../test.pl -c ../../../src/goto-cc/goto-gcc ; then \
	  ../failed-tests-printer.pl ; \
	  exit 1 ; \
	fi

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
