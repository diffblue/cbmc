DIRS = ansi-c big-int cbmc cpp goto-cc goto-instrument goto-programs \
       goto-symex langapi pointer-analysis solvers util linking xmllang \
       assembler analyses java_bytecode aa-path-symex path-symex musketeer \
       json

all: cbmc.dir goto-cc.dir goto-instrument.dir path-symex.dir json.dir

###############################################################################

util.dir: big-int.dir

# everything depends on util
$(patsubst %, %.dir, $(filter-out big-int util, $(DIRS))): util.dir

.PHONY: languages
.PHONY: clean

cpp.dir: ansi-c.dir linking.dir

languages: util.dir langapi.dir \
           cpp.dir ansi-c.dir xmllang.dir assembler.dir java_bytecode.dir

goto-instrument.dir: languages goto-programs.dir pointer-analysis.dir \
                     goto-symex.dir linking.dir analyses.dir solvers.dir

musketeer.dir: goto-instrument.dir

cbmc.dir: languages solvers.dir goto-symex.dir analyses.dir \
          pointer-analysis.dir goto-programs.dir linking.dir

goto-cc.dir: languages pointer-analysis.dir goto-programs.dir linking.dir

# building for a particular directory

$(patsubst %, %.dir, $(DIRS)):
	## Entering $(basename $@)
	$(MAKE) $(MAKEARGS) -C $(basename $@)

# generate source files

$(patsubst %, %_generated_files, $(DIRS)):
	$(MAKE) $(MAKEARGS) -C $(patsubst %_generated_files, %, $@) generated_files
	
generated_files: $(patsubst %, %_generated_files, $(DIRS))

# cleaning

clean: $(patsubst %, %_clean, $(DIRS))

$(patsubst %, %_clean, $(DIRS)):
	$(MAKE) $(MAKEARGS) -C $(patsubst %_clean, %, $@) clean ; \

# minisat 2 download, for your convenience

minisat2-download:
	@echo "Downloading Minisat 2.2.0"
	@lwp-download http://ftp.debian.org/debian/pool/main/m/minisat2/minisat2_2.2.0.orig.tar.gz
	@tar xfz minisat2_2.2.0.orig.tar.gz
	@rm -Rf ../minisat-2.2.0
	@mv minisat-2.2.0 ../minisat-2.2.0
	@(cd ../minisat-2.2.0; patch -p1 < ../scripts/minisat-2.2.0-patch)
	@rm minisat2_2.2.0.orig.tar.gz
