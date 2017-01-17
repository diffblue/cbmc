DIRS = ansi-c big-int cbmc jbmc cpp goto-cc goto-instrument goto-programs \
       goto-symex langapi pointer-analysis solvers util linking xmllang \
       assembler analyses java_bytecode \
       json goto-analyzer jsil goto-diff clobber \
       memory-models miniz

all: cbmc.dir jbmc.dir goto-cc.dir goto-instrument.dir \
     goto-analyzer.dir goto-diff.dir

###############################################################################

util.dir: big-int.dir

# everything but big-int depends on util
$(patsubst %, %.dir, $(filter-out big-int util, $(DIRS))): util.dir

.PHONY: languages
.PHONY: clean

cpp.dir: ansi-c.dir linking.dir

java_bytecode.dir: miniz.dir

languages: util.dir langapi.dir \
           cpp.dir ansi-c.dir xmllang.dir assembler.dir java_bytecode.dir \
           jsil.dir

goto-instrument.dir: languages goto-programs.dir pointer-analysis.dir \
                     goto-symex.dir linking.dir analyses.dir solvers.dir \
                     json.dir

cbmc.dir: languages solvers.dir goto-symex.dir analyses.dir \
          pointer-analysis.dir goto-programs.dir linking.dir \
          goto-instrument.dir

jbmc.dir: java_bytecode.dir cbmc.dir

goto-analyzer.dir: languages analyses.dir goto-programs.dir linking.dir \
                   json.dir goto-instrument.dir

goto-diff.dir: languages goto-programs.dir pointer-analysis.dir \
               linking.dir analyses.dir solvers.dir json.dir

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

minisat2-download:
	@echo "Downloading Minisat 2.2.1"
	@$(DOWNLOADER) http://ftp.debian.org/debian/pool/main/m/minisat2/minisat2_2.2.1.orig.tar.gz
	@tar xfz minisat2_2.2.1.orig.tar.gz
	@rm -Rf ../minisat-2.2.1
	@mv minisat2-2.2.1 ../minisat-2.2.1
	@(cd ../minisat-2.2.1; patch -p1 < ../scripts/minisat-2.2.1-patch)
	@rm minisat2_2.2.1.orig.tar.gz

glucose-download:
	@echo "Downloading glucose-syrup"
	@$(DOWNLOADER) http://www.labri.fr/perso/lsimon/downloads/softwares/glucose-syrup.tgz
	@tar xfz glucose-syrup.tgz
	@rm -Rf ../glucose-syrup
	@mv glucose-syrup ../
	@(cd ../glucose-syrup; patch -p1 < ../scripts/glucose-syrup-patch)
	@rm glucose-syrup.tgz

cprover-jar-build:
	@echo "Building org.cprover.jar"
	@(cd java_bytecode/library/; \
	mkdir -p target; \
	javac -d target/ `find src/ -name "*.java"`; \
	cd target; jar cf org.cprover.jar `find . -name "*.class"`; \
	mv org.cprover.jar ../../../)

ipasir-download:
	# get the 2016 version of the ipasir package, which contains a few solvers
	@echo "Download ipasir 2016 package"
	@(lwp-download http://baldur.iti.kit.edu/sat-competition-2016/downloads/ipasir.zip ../ipasir.zip)
	@(cd ..; unzip -u ipasir.zip)

ipasir-build: ipasir-download
	# build libpicosat, and create a libipasir.a in ipasir directory
	# make sure that the ipasir.h file is located there as well (ships with 2016 package)
	@echo "Build Picosat 961 from ipasir 2016 package"
	$(MAKE) -C ../ipasir/sat/picosat961 libipasirpicosat961.a
	@(cd ../ipasir; ln -sf sat/picosat961/libipasirpicosat961.a libipasir.a)

.PHONY: ipasir-build minisat2-download glucose-download cprover-jar-build
