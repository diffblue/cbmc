################################################################
# Configuration

# Package version number (cbmc version number)
VERSION=5.12

# Suffix to use to distinguish a develop/HEAD build from a release
LATEST=-latest

# Debian package version to fetch debian/ folder from
DEBIAN_BASE=5.12-5

################################################################

default: build

cbmc_$(VERSION).orig-java-models-library.tar.gz:
	curl -L -o $@ https://github.com/diffblue/java-models-library/archive/master.tar.gz

cbmc_$(VERSION).orig.tar.gz:
ifeq (,$(LATEST))
	curl -o $@ https://github.com/diffblue/cbmc/archive/cbmc-$(VERSION).tar.gz
else
	curl -o $@ -L https://github.com/diffblue/cbmc/tarball/develop
endif

cbmc-$(VERSION): cbmc_$(VERSION).orig.tar.gz
	tar xzf $<
ifeq (,$(LATEST))
	mv cbmc-cbmc-$(VERSION) $@
else
	mv diffblue-cbmc-* $@
endif

cbmc-$(VERSION)/java-models-library: cbmc-$(VERSION) cbmc_$(VERSION).orig-java-models-library.tar.gz
	cd $< && tar xzf ../cbmc_$(VERSION).orig-java-models-library.tar.gz
	mv $</java-models-library-master $</java-models-library

cbmc-$(VERSION)/debian: cbmc-$(VERSION)
	# should get existing artifacts instead
	curl -o debian.tar.xz http://deb.debian.org/debian/pool/main/c/cbmc/cbmc_$(DEBIAN_BASE).debian.tar.xz
	cd $< && tar xJf ../debian.tar.xz
	$(RM) debian.tar.xz

cbmc-$(VERSION)/debian/changelog: cbmc-$(VERSION)/debian
	cd cbmc-$(VERSION) && \
	if dpkg --compare-versions `dpkg-parsechangelog -S Version` lt $(VERSION) ; then \
		NEW_VERSION=$(VERSION)-1~auto1 ; \
	else \
	  MINOR=`dpkg-parsechangelog -S Version | cut -f2 -d- | cut -f1 -d.` ; \
		NEW_VERSION=$(VERSION)-`expr $$MINOR + 1`~auto1 ; \
	fi ; \
	cp debian/changelog debian/changelog.orig ; \
	cd .. ; \
	cp changelog $@ ; \
	sed -i "s/#VERSION#/$$NEW_VERSION/" $@
	sed -i "s/#DATE#/`date -R`/" $@
	cat cbmc-$(VERSION)/debian/changelog.orig >> $@
	$(RM) cbmc-$(VERSION)/debian/changelog.orig

build: cbmc-$(VERSION)/debian/changelog cbmc-$(VERSION)/java-models-library
	sudo apt-get -y install quilt
	cd cbmc-$(VERSION) && export QUILT_PATCHES=debian/patches && \
		while quilt push; do quilt refresh; done && quilt pop -a
	$(RM) cbmc-$(VERSION)/debian/patches/*~
	sudo apt-get -y install \
		debhelper minisat zlib1g-dev flex bison default-jdk-headless \
		maven maven-repo-helper maven-debian-helper libmaven-compiler-plugin-java
ifneq (,$(LATEST))
	sed -i "s/^Package: cbmc.*/Package: cbmc$(LATEST)/" cbmc-$(VERSION)/debian/control
	sed -i "s#usr/bin#usr/local/cbmc$(LATEST)/bin#" cbmc-$(VERSION)/debian/dirs
	sed -i "s#usr/bin#usr/local/cbmc$(LATEST)/bin#" cbmc-$(VERSION)/debian/install
	sed -i "s#usr/bin#usr/local/cbmc$(LATEST)/bin#" cbmc-$(VERSION)/debian/links
	echo "override_dh_usrlocal:" >> cbmc-$(VERSION)/debian/rules
	echo "\ttrue" >> cbmc-$(VERSION)/debian/rules
	echo "override_dh_dwz:" >> cbmc-$(VERSION)/debian/rules
	echo "\ttrue" >> cbmc-$(VERSION)/debian/rules
	$(RM) cbmc-$(VERSION)/debian/manpages
	sed -i "/share\/man\/man1/d" cbmc-$(VERSION)/debian/links
endif
	DEBHELPER_VERSION=`dpkg -l debhelper | tail -n1 | awk '{print $$3}' | cut -f1 -d.` ; \
		if [ $$DEBHELPER_VERSION -lt 12 ] ; then \
			echo $$DEBHELPER_VERSION > cbmc-$(VERSION)/debian/compat ; \
			if [ $$DEBHELPER_VERSION -lt 10 ] ; then \
			  sed -i 's/^\tdh $$@/\tdh $$@ --parallel/' cbmc-$(VERSION)/debian/rules ; \
			fi ; \
		fi
	PLUGIN_VERSION=`dpkg -l libmaven-compiler-plugin-java | tail -n1 | awk '{print $$3}' | cut -f1 -d-` ; \
		sed -i "s/^\(+[[:space:]]*<version>\).*<\/version>/\1$$PLUGIN_VERSION<\/version>/" \
		cbmc-$(VERSION)/debian/patches/maven*
	# the following to changes should really become part of the standard Debian
	# build rules
	sed -i '11s/^$$/parallel = $$(patsubst parallel=\%,\%,$$(filter parallel=\%,$$(DEB_BUILD_OPTIONS)))/' \
		cbmc-$(VERSION)/debian/rules
	sed -i 's/$$(MAKE)/$$(MAKE) -j$$(parallel)/' cbmc-$(VERSION)/debian/rules
	cd cbmc-$(VERSION) && dpkg-buildpackage -b -Jauto -uc -d
	# upload new artifacts

clean:
	$(RM) -r cbmc-$(VERSION)
	$(RM) cbmc_$(VERSION).orig.tar.gz
	$(RM) cbmc_$(VERSION).orig-java-models-library.tar.gz

.PHONY: build clean default
