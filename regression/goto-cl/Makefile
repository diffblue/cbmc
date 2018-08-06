default: tests.log

test:
	@../test.pl -p -c ../../../src/goto-cc/goto-cl -X goto-link
	@cp ../../src/goto-cc/goto-cl.exe ../../src/goto-cc/goto-link.exe
	@../test.pl -p -c ../../../src/goto-cc/goto-link -I goto-link

tests.log: ../test.pl
	@../test.pl -p -c ../../../src/goto-cc/goto-cl -X goto-link
	@cp ../../src/goto-cc/goto-cl.exe ../../src/goto-cc/goto-link.exe
	@../test.pl -p -c ../../../src/goto-cc/goto-link -I goto-link

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
	find -name '*.exe' -execdir $(RM) '{}' \;
	find -name '*.goto-cc-saved' -execdir $(RM) '{}' \;
	$(RM) tests.log
