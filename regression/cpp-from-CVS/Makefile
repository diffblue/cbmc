default: tests.log

test:
	@../test.pl -c cbmc

tests.log: ../test.pl
	@../test.pl -c cbmc

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/main.c" "$$dir/main.out"; \
		fi; \
	done;
