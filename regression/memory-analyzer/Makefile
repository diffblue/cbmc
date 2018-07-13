default: clean tests.log

clean:
	find -name '*.exe' -execdir $(RM) '{}' \;
	find -name '*.out' -execdir $(RM) '{}' \;
	$(RM) tests.log

test:
	-@ln -s goto-cc ../../src/goto-cc/goto-gcc
	@../test.pl -p -c ../compile_example.sh

tests.log: ../test.pl
	-@ln -s goto-cc ../../src/goto-cc/goto-gcc
	@../test.pl -p -c ../compile_example.sh

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.c" "$$dir/*.out"; \
		fi; \
	done;
