default:
	@echo nothing to do

test:
	@python3 test.py

clean:
	$(RM) -rf */html

pylint:
	pylint --extension-pkg-whitelist=lxml test.py

