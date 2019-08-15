default:
	@echo nothing to do

test:
	@python3 test.py

clean:
	-find . -name html -type d -prune -exec rm -rf {} \;
	-find . -name coverage.xml -exec rm -rf {} \;
	-find . -name property.xml -exec rm -rf {} \;
	-find . -name cbmc.log     -exec rm -rf {} \;

pylint:
	pylint --extension-pkg-whitelist=lxml test.py
