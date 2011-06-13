DIRS = ansi-c big-int cbmc cpp goto-cc goto-instrument goto-programs \
       goto-symex langapi pointer-analysis solvers util xmllang

all: cbmc.dir goto-cc.dir goto-instrument.dir

include config.inc
include common

###############################################################################

util.dir: big-int.dir

# everything depends on util
$(patsubst %, %.dir, $(filter-out big-int util, $(DIRS))): util.dir

languages: util.dir langapi.dir \
           cpp.dir ansi-c.dir xmllang.dir

goto-instrument.dir: languages goto-programs.dir pointer-analysis.dir

cbmc.dir: languages solvers.dir goto-symex.dir \
          pointer-analysis.dir goto-programs.dir goto-symex.dir

goto-cc.dir: languages pointer-analysis.dir goto-programs.dir

$(patsubst %, %.dir, $(DIRS)):
	## Entering $(basename $@)
	$(MAKE) $(MAKEARGS) -C $(basename $@)

clean: $(patsubst %, %_clean, $(DIRS))
	rm -f *.o $(shell find . -name "*.d")

dep: $(patsubst %, %_dep, $(DIRS))

$(patsubst %, %_clean, $(DIRS)):
	if [ -e $(patsubst %_clean, %, $@)/. ] ; then \
		$(MAKE) $(MAKEARGS) -C $(patsubst %_clean, %, $@) clean ; \
	fi

$(patsubst %, %_dep, $(DIRS)):
	if [ -e $(patsubst %_dep, %, $@)/. ] ; then \
		$(MAKE) $(MAKEARGS) -C $(patsubst %_dep, %, $@) dep ; \
	fi
