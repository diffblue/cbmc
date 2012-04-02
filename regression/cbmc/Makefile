default: tests.log

test:
	@../test.pl -c cbmc

tests.log: ../test.pl
	@../test.pl -c cbmc

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.c" "$$dir/*.out"; \
		fi; \
	done;
