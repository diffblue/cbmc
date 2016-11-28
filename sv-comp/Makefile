all: 
	mkdir -p tmp
	cp ../LICENSE cbmc tmp/
	cp ../src/cbmc/cbmc tmp/cbmc-binary
	cd tmp; tar cfz ../CBMC-sv-comp-2017.tar.gz *; rm cbmc cbmc-binary LICENSE; cd ..; rm -R tmp
