default: tests.log

test:
	@../test.pl -c ../run.sh

tests.log: ../test.pl
	@../test.pl -c ../run.sh

clean:
	@for dir in *; do \
                if [ -d "$$dir" ]; then \
                        rm $$dir/*.txt $$dir/*.dot $$dir/*.gb $$dir/*.out; \
                fi; \
        done;

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.c" "$$dir/*.out"; \
		fi; \
	done;
