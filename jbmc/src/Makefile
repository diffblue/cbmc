DIRS = janalyzer jbmc jdiff java_bytecode miniz
ROOT = ../

include config.inc

.PHONY: all
all: janalyzer.dir jbmc.dir jdiff.dir library

# building cbmc proper
.PHONY: cprover.dir
cprover.dir:
	$(MAKE) $(MAKEARGS) -C $(CPROVER_DIR)/src

.PHONY: java_bytecode.dir
java_bytecode.dir: miniz.dir

.PHONY: janalyzer.dir
janalyzer.dir: java_bytecode.dir cprover.dir

.PHONY: jbmc.dir
jbmc.dir: java_bytecode.dir cprover.dir

.PHONY: jdiff.dir
jdiff.dir: java_bytecode.dir cprover.dir

.PHONY: miniz.dir
miniz.dir:

LIBRARY_DIR = ../lib/java-models-library

clean: clean_library

.PHONY: clean_library
clean_library:
	rm -rf core-models.jar
	if [ -d $(LIBRARY_DIR) ]; then cd $(LIBRARY_DIR); mvn clean; fi

.PHONY: library
library:
	if [ -d $(LIBRARY_DIR) ]; then (cd $(LIBRARY_DIR); mvn package); cp $(LIBRARY_DIR)/target/core-models.jar java_bytecode/library/ ; fi

$(patsubst %, %.dir, $(DIRS)):
	## Entering $(basename $@)
	$(MAKE) $(MAKEARGS) -C $(basename $@)

# generate source files

$(patsubst %, %_generated_files, $(DIRS)):
	$(MAKE) $(MAKEARGS) -C $(patsubst %_generated_files, %, $@) generated_files

.PHONY: generated_files
generated_files: $(patsubst %, %_generated_files, $(DIRS))

# cleaning

.PHONY: clean
clean: $(patsubst %, %_clean, $(DIRS)) cprover_clean dist_clean

$(patsubst %, %_clean, $(DIRS)):
	$(MAKE) $(MAKEARGS) -C $(patsubst %_clean, %, $@) clean ; \

.PHONY: cprover_clean
cprover_clean:
	$(MAKE) $(MAKEARGS) -C $(CPROVER_DIR)/src clean

.PHONY: dist_clean
dist_clean:
	rm -rf $(ROOT)dist

setup-submodules:
	git submodule update --init

.PHONY: dist
dist: setup-submodules all
	mkdir -p $(ROOT)dist/lib
	cp ../lib/java-models-library/target/core-models.jar $(ROOT)dist/lib
	mkdir -p $(ROOT)dist/bin
	cp jbmc/jbmc $(ROOT)dist/bin
	cp janalyzer/janalyzer $(ROOT)dist/bin
	cp jdiff/jdiff $(ROOT)dist/bin
