default: tests.log

test:
	@./test.sh

tests.log: ../test.pl
	@./test.sh

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.java" "$$dir/*.out"; \
		fi; \
	done;

clean:
	find . -name '*.*~' | xargs rm -f
	find . -name '*.out' | xargs rm -f
	find . -name '*.o' | xargs rm -f
	rm -f tests.log	
