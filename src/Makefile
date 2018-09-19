DIRS = analyses \
       ansi-c \
       assembler \
       big-int \
       cbmc \
       cpp \
       goto-analyzer \
       goto-cc \
       goto-diff \
       goto-instrument \
       goto-programs \
       goto-symex \
       jsil \
       json \
       langapi \
       linking \
       pointer-analysis \
       solvers \
       util \
       xmllang \
       # Empty last line

all: cbmc.dir \
     goto-analyzer.dir \
     goto-cc.dir \
     goto-diff.dir \
     goto-instrument.dir \
     # Empty last line

###############################################################################

util.dir: big-int.dir

# everything but big-int depends on util
$(patsubst %, %.dir, $(filter-out big-int util, $(DIRS))): util.dir

.PHONY: languages
.PHONY: clean

cpp.dir: ansi-c.dir linking.dir

languages: util.dir langapi.dir \
           cpp.dir ansi-c.dir xmllang.dir assembler.dir \
           jsil.dir

solvers.dir: util.dir langapi.dir

goto-instrument.dir: languages goto-programs.dir pointer-analysis.dir \
                     goto-symex.dir linking.dir analyses.dir solvers.dir \
                     json.dir

cbmc.dir: languages solvers.dir goto-symex.dir analyses.dir \
          pointer-analysis.dir goto-programs.dir linking.dir \
          goto-instrument.dir

goto-analyzer.dir: languages analyses.dir goto-programs.dir linking.dir \
                   json.dir goto-instrument.dir

goto-diff.dir: languages goto-programs.dir pointer-analysis.dir \
               linking.dir analyses.dir goto-instrument.dir \
               solvers.dir json.dir goto-symex.dir

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

# minisat2 and glucose download, for your convenience

DOWNLOADER = lwp-download
TAR = tar

minisat2-download:
	@echo "Downloading Minisat 2.2.1"
	@$(DOWNLOADER) http://ftp.debian.org/debian/pool/main/m/minisat2/minisat2_2.2.1.orig.tar.gz
	@$(TAR) xfz minisat2_2.2.1.orig.tar.gz
	@rm -Rf ../minisat-2.2.1
	@mv minisat2-2.2.1 ../minisat-2.2.1
	@(cd ../minisat-2.2.1; patch -p1 < ../scripts/minisat-2.2.1-patch)
	@rm minisat2_2.2.1.orig.tar.gz

glucose-download:
	@echo "Downloading glucose-syrup"
	@$(DOWNLOADER) http://www.labri.fr/perso/lsimon/downloads/softwares/glucose-syrup.tgz
	@$(TAR) xfz glucose-syrup.tgz
	@rm -Rf ../glucose-syrup
	@mv glucose-syrup ../
	@(cd ../glucose-syrup; patch -p1 < ../scripts/glucose-syrup-patch)
	@rm glucose-syrup.tgz

cadical_release = rel-06w
cadical-download:
	@echo "Downloading CaDiCaL $(cadical_release)"
	@curl -L https://github.com/arminbiere/cadical/archive/$(cadical_release).tar.gz | tar xz
	@rm -Rf ../cadical
	@mv cadical-$(cadical_release) ../cadical
	@(cd ../cadical; patch -p1 < ../scripts/cadical-patch)
	@cd ../cadical && CXX=$(CXX) CXXFLAGS=-O3 ./configure --debug && make

doc :
	doxygen

.PHONY: ipasir-build minisat2-download glucose-download
