DIRS = ansi-c big-int cbmc cpp goto-cc goto-instrument goto-programs \
       goto-symex langapi pointer-analysis solvers util linking xmllang \
       assembler analyses

all: cbmc.dir goto-cc.dir goto-instrument.dir

###############################################################################

util.dir: big-int.dir

# everything depends on util
$(patsubst %, %.dir, $(filter-out big-int util, $(DIRS))): util.dir

.PHONY: languages
.PHONY: clean

languages: util.dir langapi.dir \
           cpp.dir ansi-c.dir xmllang.dir assembler.dir

goto-instrument.dir: languages goto-programs.dir pointer-analysis.dir \
                     goto-symex.dir linking.dir analyses.dir

cbmc.dir: languages solvers.dir goto-symex.dir analyses.dir \
          pointer-analysis.dir goto-programs.dir linking.dir

goto-cc.dir: languages pointer-analysis.dir goto-programs.dir linking.dir

$(patsubst %, %.dir, $(DIRS)):
	## Entering $(basename $@)
	$(MAKE) $(MAKEARGS) -C $(basename $@)

clean: $(patsubst %, %_clean, $(DIRS))

$(patsubst %, %_clean, $(DIRS)):
	if [ -e $(patsubst %_clean, %, $@)/. ] ; then \
		$(MAKE) $(MAKEARGS) -C $(patsubst %_clean, %, $@) clean ; \
	fi

minisat2-download:
	@echo "Downloading Minisat 2.2.0"
	@lwp-download http://minisat.se/downloads/minisat-2.2.0.tar.gz
	@tar xfz minisat-2.2.0.tar.gz
	@rm -Rf ../minisat-2.2.0
	@mv minisat ../minisat-2.2.0
	@rm minisat-2.2.0.tar.gz

