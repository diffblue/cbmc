default:
	@Nothing to do

clean:
	$(RM) *.pyc
	$(RM) *~ .*~ \#* .\#*

veryclean: clean

################################################################

lint: pylint pycodestyle pydocstyle

pylint:
	-pylint *.py --disable=duplicate-code,invalid-name

pycodestyle:
	-pycodestyle *.py

pydocstyle:
	-pydocstyle *.py

test:
	./test.sh

################################################################

.PHONY: default clean veryclean
.PHONY: line pylint pycodestyle pydocstyle test
