default: tests.log

test:
	-@ln -s goto-cc ../../src/goto-cc/goto-gcc
	@../test.pl -p -c ../../../src/goto-cc/goto-gcc

tests.log: ../test.pl
	-@ln -s goto-cc ../../src/goto-cc/goto-gcc
	@../test.pl -p -c ../../../src/goto-cc/goto-gcc

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
