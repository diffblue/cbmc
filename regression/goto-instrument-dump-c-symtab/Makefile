default: tests.log

include ../../src/config.inc
include ../../src/common

test:
	@../test.pl -e -p -c '../chain.sh ../../../src/symtab2gb/symtab2gb ../../../src/goto-instrument/goto-instrument $(exe)'

tests.log:
	@../test.pl -e -p -c '../chain.sh ../../../src/symtab2gb/symtab2gb ../../../src/goto-instrument/goto-instrument $(exe)'

clean:
	$(RM) tests.log
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			cd "$$dir"; \
			$(RM) *.out *.gb *.dump.c *.recompiled.gb; \
			cd ..; \
		fi \
	done
