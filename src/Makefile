DIRS = ansi-c big-int cbmc cprover csp ebmc hoare \
       infrules intrep solvers pvs separate smvlang util verilog \
       vhdl langapi netlist cpp pascal symex termination \
       satqe satmc satabs explain specc xmllang promela \
       goto-programs bplang vcegar hw-cbmc vsynth \
       boppo pointer-analysis cogent goto-instrument \
       goto-symex ipp prover trans bv_refinement mcp goto-cc \
       smtlang php cemc interpolation scoot floatbv cover \
       scratch ai k-induction

all: cprover.dir cbmc.dir ebmc.dir cogent.dir \
     satabs.dir hw-cbmc.dir promela.dir \
     boppo.dir goto-cc.dir goto-instrument.dir cover.dir

include config.inc
include common

###############################################################################

util.dir: big-int.dir

languages: util.dir langapi.dir \
           ansi-c.dir intrep.dir smvlang.dir \
           xmllang.dir promela.dir bplang.dir

goto-instrument.dir: goto-programs.dir languages pointer-analysis.dir

cogent.dir: ansi-c.dir util.dir solvers.dir

cprover.dir: languages

cbmc.dir: languages solvers.dir goto-symex.dir \
          pointer-analysis.dir goto-programs.dir goto-symex.dir

cover.dir: cbmc.dir

ivt.dir: languages solvers.dir goto-symex.dir \
         pointer-analysis.dir goto-programs.dir goto-symex.dir

cemc.dir: cbmc.dir

scoot.dir: satabs.dir languages

goto-cc.dir: languages pointer-analysis.dir goto-programs.dir

hw-cbmc.dir: cbmc.dir trans.dir

boppo.dir: langapi.dir bplang.dir promela.dir util.dir \
           solvers.dir languages

explain.dir: cbmc.dir

satabs.dir: languages goto-symex.dir goto-programs.dir \
            pointer-analysis.dir solvers.dir

vcegar.dir: languages satqe.dir solvers.dir ebmc.dir

vsynth.dir: langapi.dir verilog.dir util.dir vhdl.dir netlist.dir

ebmc.dir: solvers.dir languages trans.dir

satmc.dir: solvers.dir smvlang.dir util.dir verilog.dir languages \
           intrep.dir vhdl.dir netlist.dir trans.dir satqe.dir
k-induction.dir: cbmc.dir ai.dir

scratch.dir: k-induction.dir

ai.dir: cbmc.dir

ifdef MODULE_INTERPOLATION
ebmc.dir: interpolation.dir
interpolation.dir: solvers.dir langapi.dir util.dir
endif

ifdef MODULE_PROVER
satabs.dir: prover.dir
ebmc.dir: prover.dir
endif

ifdef MODULE_IPP
satabs.dir: ipp.dir
endif

ifdef MODULE_BV_REFINEMENT
cbmc.dir: bv_refinement.dir
endif

ifdef MODULE_SATQE
satabs.dir: satqe.dir
all: satmc.dir
endif

ifdef MODULE_SMTLANG
languages: smtlang.dir
endif

ifdef MODULE_CPP
languages: cpp.dir
endif

ifdef MODULE_PHP
languages: php.dir
endif

ifdef MODULE_CSP
languages: csp.dir
endif

ifdef MODULE_PVS
languages: pvs.dir
endif

ifdef MODULE_VERILOG
languages: verilog.dir
endif

ifdef MODULE_VHDL
languages: vhdl.dir
endif

ifdef MODULE_NETLIST
languages: netlist.dir
endif

ifdef MODULE_SPECC
languages: specc.dir
endif

ifdef MODULE_PASCAL
languages: pascal.dir
endif

ifdef MODULE_HWCBMC
satabs: hw-cbmc.dir
all: hw-cbmc.dir
endif

ifdef MODULE_CEMC
all: cemc.dir
endif

ifdef MODULE_FLOATBV
solvers.dir: floatbv.dir
endif

$(patsubst %, %.dir, $(DIRS)):
	## Entering $(basename $@)
	$(MAKE) $(MAKEARGS) -C $(basename $@)

clean: $(patsubst %, %_clean, $(DIRS))
	rm -f *.o

dep: $(patsubst %, %_dep, $(DIRS))

$(patsubst %, %_clean, $(DIRS)):
	if [ -e $(patsubst %_clean, %, $@)/. ] ; then \
		$(MAKE) $(MAKEARGS) -C $(patsubst %_clean, %, $@) clean ; \
	fi

$(patsubst %, %_dep, $(DIRS)):
	if [ -e $(patsubst %_dep, %, $@)/. ] ; then \
		$(MAKE) $(MAKEARGS) -C $(patsubst %_dep, %, $@) dep ; \
	fi
