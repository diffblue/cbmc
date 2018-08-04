default: tests.log

test:
	@../test.pl -p -c ../../../src/goto-cc/goto-cl

tests.log: ../test.pl
	@../test.pl -p -c ../../../src/goto-cc/goto-cl

show:
	@for dir in *; do \
	  if [ -d "$$dir" ]; then \
	    vim -o "$$dir/*.c" "$$dir/*.out"; \
	  fi; \
	done;

clean:
	find -name '*.out' -execdir $(RM) '{}' \;
	find -name '*.gb' -execdir $(RM) '{}' \;
	find -name '*.obj' -execdir $(RM) '{}' \;
	find -name '*.goto-cc-saved' -execdir $(RM) '{}' \;
	$(RM) tests.log
