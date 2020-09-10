PKG_STABLE_NAME = cbmc
PKG_LATEST_NAME = cbmc-latest
PKG_STABLE_TAR = $(PKG_STABLE_NAME).tar.gz
PKG_LATEST_TAR = $(PKG_LATEST_NAME).tar.gz

REPODIR ?= .

default: stable latest

stable: $(PKG_STABLE_TAR)

latest: $(PKG_LATEST_TAR)

$(REPODIR)/build/bin/cbmc:
	brew install cmake ninja openjdk maven
	# See https://github.com/diffblue/cbmc/issues/4956 for clang issue
	cd $(REPODIR) && cmake -S. -Bbuild -DCMAKE_C_COMPILER=/usr/bin/clang -DWITH_JBMC=YES -GNinja
	cd $(REPODIR) && cmake --build build

$(PKG_STABLE_TAR): $(REPODIR)/build/bin/cbmc
	$(RM) -r ${PKG_STABLE_NAME}

	mkdir -p ${PKG_STABLE_NAME}/bin
	cp $(REPODIR)/build/bin/cbmc ${PKG_STABLE_NAME}/bin
	cp $(REPODIR)/build/bin/goto-analyzer ${PKG_STABLE_NAME}/bin
	cp $(REPODIR)/build/bin/goto-cc ${PKG_STABLE_NAME}/bin
	cp $(REPODIR)/build/bin/goto-diff ${PKG_STABLE_NAME}/bin
	cp $(REPODIR)/build/bin/goto-gcc ${PKG_STABLE_NAME}/bin
	cp $(REPODIR)/build/bin/goto-harness ${PKG_STABLE_NAME}/bin
	cp $(REPODIR)/build/bin/goto-instrument ${PKG_STABLE_NAME}/bin
	cp $(REPODIR)/build/bin/goto-ld ${PKG_STABLE_NAME}/bin
	cp $(REPODIR)/build/bin/janalyzer ${PKG_STABLE_NAME}/bin
	cp $(REPODIR)/build/bin/java-unit ${PKG_STABLE_NAME}/bin
	cp $(REPODIR)/build/bin/jbmc ${PKG_STABLE_NAME}/bin
	cp $(REPODIR)/build/bin/jdiff ${PKG_STABLE_NAME}/bin

	mkdir -p ${PKG_STABLE_NAME}/share/man/man1
	cp $(REPODIR)/doc/man/cbmc.1 ${PKG_STABLE_NAME}/share/man/man1

	tar fcz ${PKG_STABLE_TAR} ${PKG_STABLE_NAME}

$(PKG_LATEST_TAR): $(REPODIR)/build/bin/cbmc
	$(RM) -r ${PKG_LATEST_NAME}

	mkdir -p ${PKG_LATEST_NAME}/bin
	cp $(REPODIR)/build/bin/cbmc ${PKG_LATEST_NAME}/bin
	cp $(REPODIR)/build/bin/goto-analyzer ${PKG_LATEST_NAME}/bin
	cp $(REPODIR)/build/bin/goto-cc ${PKG_LATEST_NAME}/bin
	cp $(REPODIR)/build/bin/goto-diff ${PKG_LATEST_NAME}/bin
	cp $(REPODIR)/build/bin/goto-gcc ${PKG_LATEST_NAME}/bin
	cp $(REPODIR)/build/bin/goto-harness ${PKG_LATEST_NAME}/bin
	cp $(REPODIR)/build/bin/goto-instrument ${PKG_LATEST_NAME}/bin
	cp $(REPODIR)/build/bin/goto-ld ${PKG_LATEST_NAME}/bin
	cp $(REPODIR)/build/bin/janalyzer ${PKG_LATEST_NAME}/bin
	cp $(REPODIR)/build/bin/java-unit ${PKG_LATEST_NAME}/bin
	cp $(REPODIR)/build/bin/jbmc ${PKG_LATEST_NAME}/bin
	cp $(REPODIR)/build/bin/jdiff ${PKG_LATEST_NAME}/bin

	mkdir -p ${PKG_LATEST_NAME}/share/man/man1
	cp $(REPODIR)/doc/man/cbmc.1 ${PKG_LATEST_NAME}/share/man/man1

	tar fcz ${PKG_LATEST_TAR} ${PKG_LATEST_NAME}

clean:
	$(RM) *~
	$(RM) -r $(PKG_STABLE_TAR) $(PKG_STABLE_NAME)
	$(RM) -r $(PKG_LATEST_TAR) $(PKG_LATEST_NAME)

.PHONY: default stable latest clean
