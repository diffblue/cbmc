default: markdown doc api adr assets cprover-manual man

markdown:
	cd .. && bash doxygen-root/doxygen-markdown/markdown.sh

doc:
	doxygen doxyfile

api:
	cd ../API && doxygen ../doxygen-root/doxyfile-doc-api
	mkdir -p html/api
	cp -r api/html/* html/api

adr:
	cd ../ADR && doxygen ../doxygen-root/doxyfile-doc-adr
	mkdir -p html/adr
	cp -r adr/html/* html/adr

assets:
	cd ../assets && doxygen ../doxygen-root/doxyfile-doc-assets
	mkdir -p html/assets
	cp -r assets/html/* html/assets
	cp ../assets/*.png html/assets

cprover-manual:
	cd ../cprover-manual && doxygen ../doxygen-root/doxyfile-doc-cprover-manual
	mkdir -p html/cprover-manual
	cp -r cprover-manual/html/* html/cprover-manual
	cp ../cprover-manual/*.c html/cprover-manual

man:
	mkdir -p html/man
	for man in ../man/*.1; do pandoc $$man > html/man/$$(basename $$man .1).html; done


clean:
	$(RM) -r api adr assets html cprover-manual man

.PHONY: markdown doc api adr assets cprover-manual man clean
