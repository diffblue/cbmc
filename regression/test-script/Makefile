
default: tests.log

test:
	@../test.pl -p -c ../program_runner.sh

	@echo "Testing KNOWNBUG fail"

	@../test.pl -e -p -c ../program_runner.sh -K

tests.log:
	pwd
	@../test.pl -e -p -c ../program_runner.sh

	@echo "Testing KNOWNBUG fail"

	@../test.pl -e -p -c ../program_runner.sh -K

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.c" "$$dir/*.out"; \
		fi; \
	done;

clean:
	@for dir in *; do \
		$(RM) tests.log; \
		if [ -d "$$dir" ]; then \
			cd "$$dir"; \
			$(RM) *.out *.gb; \
			cd ..; \
		fi \
	done
