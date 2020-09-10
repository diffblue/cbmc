################################################################
# Configuration

# CBMC
#
# CBMC name: The stable package will be $(CBMC_NAME) and the develop
# package will be $(CBMC_NAME)-latest.
#
# CBMC version: The version number returned by `cbmc --version`.

CBMC_NAME = cbmc
CBMC_VERSION = 5.12

# Builds
#
# GITHUB: Build using a clone of the GitHub repository if GITHUB is
# nonempty, and build by downloading tarballs if it is not.  If GITHUB
# is nonempty, the GitHub repository must be a subdirectory of the
# directory containing this Makefile, and it must be named
# $(CBMC_NAME)-$(CBMC_VERSION).
#
# STABLE: When GITHUB is not nonempty and we are downloading tarballs,
# download the tagged commit $(CBMC_NAME)-$(CBMC_VERSION) if STABLE is
# nonempty and download the tip of the develop branch if it is not.
# Regardless of whether GITHUB is nonempty or not, install into
# /usr/bin if STABLE is nonempty and into /usr/local/cbmc-latest/bin if
# it is not.

STABLE=
GITHUB=

# Packages
#
# PKG_NAME: The name of the package, typically cbmc or cbmc-latest
# PKG_VERSION: The version of the package, typically 5.12-1
# PKG_OS: The Ubuntu code name, typically xenial or bionic or focal
#
# The name defaults to cbmc or cbmc-latest.  The version defaults to a
# value computed from the most recent package, but is typically given
# on the command line when building from GitHub.  The os defaults to
# the value given in /etc/os-release.
#
# Package version used in changelog: $(PKG_VERSION)~$(PKG_OS)
# Package name: $(PKG_NAME)_$(PKG_VERSION)~$(PKG_OS)_amd64.deb

ifneq ($(STABLE),)
PKG_NAME = $(CBMC_NAME)
else
PKG_NAME = $(CBMC_NAME)-latest
endif

#PKG_VERSION =

PKG_OS = `lsb_release -c | awk '{ print $$2 }'`

# Debian packaging
#
# DEBIAN_BASE: The Debian version to fetch the debian folder from.
# This Makefile downloads cbmc_$(DEBIAN_BASE).debian.tar.xz from
# Debian and uses its contents as the starting point for the debian
# folder for this package.

DEBIAN_BASE=5.12-5

################################################################

default: build

SRCDIR=$(CBMC_NAME)-$(CBMC_VERSION)

################################################################
# Assemble the source tree in $(SRCDIR)
#

ifeq ($(GITHUB),)
# GITHUB is empty, so assemble the source tree from tarballs

## Download the source tree
$(CBMC_NAME)_$(CBMC_VERSION).orig.tar.gz:
ifneq ($(STABLE),)
	# For the stable release, download the tagged commit
	curl -o $@ -L \
	  https://github.com/diffblue/cbmc/archive/cbmc-$(CBMC_VERSION).tar.gz
else
	# For the latest release, download latest commit on the develop branch
	curl -o $@ -L \
	  https://github.com/diffblue/cbmc/tarball/develop
endif

## Download the java models library submoduled into the cbmc repository
$(CBMC_NAME)_$(CBMC_VERSION).orig-java-models-library.tar.gz:
	curl -o $@ -L \
	  https://github.com/diffblue/java-models-library/archive/master.tar.gz

## Extract the source tree
$(SRCDIR): $(CBMC_NAME)_$(CBMC_VERSION).orig.tar.gz
	tar xzf $<
ifneq ($(STABLE),)
	mv cbmc-cbmc-$(CBMC_VERSION) $@
else
	mv diffblue-cbmc-* $@
endif

## Extract the java models library.  The Debian patch files expect this
## library to be at the top level and not under src/jbmc where it is
## submoduled into the cbmc repository.
$(SRCDIR)/java-models-library: \
		$(SRCDIR) \
		$(CBMC_NAME)_$(CBMC_VERSION).orig-java-models-library.tar.gz
	cd $< && tar xzf ../$(CBMC_NAME)_$(CBMC_VERSION).orig-java-models-library.tar.gz
	mv $</java-models-library-master $</java-models-library

else
# GITHUB is nonempty, so use the GitHub repository in $(SRCDIR).

## Create source tarball for Debian from the repository
$(CBMC_NAME)_$(CBMC_VERSION).orig.tar.gz:
	tar fcz $@ $(SRCDIR) \
		--exclude java-models-library  --exclude debian \
		--exclude-vcs --exclude-vcs-ignores  --exclude .github

## Move the java models library to where the Debian patch files expect
## to find them.
$(SRCDIR)/java-models-library:
	mv $(SRCDIR)/jbmc/lib/java-models-library $@

endif

#
# End Assemble the source tree
################################################################

################################################################
# Assemble the debian directory
#

# We download the debian directory from the debian repository, but
# Ubuntu16 requires the use of clang due to some unicode bugs in
# libraries with the default gcc.
#
# NOTE: We should use existing artifacts instead.

DEBIAN_TARBALL=http://deb.debian.org/debian/pool/main/c/cbmc/cbmc_$(DEBIAN_BASE).debian.tar.xz
XENIAL_TARBALL=https://launchpad.net/~mt-debian/+archive/ubuntu/cbmc-backports/+sourcefiles/cbmc/5.12-5~xenial10/cbmc_5.12-5~xenial10.debian.tar.xz

# Download the debian directory.
$(SRCDIR)/debian: $(SRCDIR)
	echo Found PKG_OS=$(PKG_OS)
	if [ "$(PKG_OS)" = "xenial" ] ; then \
	  echo Downloading $(XENIAL_TARBALL); \
	  curl -L -o debian.tar.xz $(XENIAL_TARBALL); \
	  sudo apt-get -y install clang-3.8 libc++-dev libc++abi-dev; \
	else \
	  echo Downloading $(DEBIAN_TARBALL); \
	  curl -L -o debian.tar.xz $(DEBIAN_TARBALL); \
	fi
	cd $< && tar xJf ../debian.tar.xz
	$(RM) debian.tar.xz

# Update the debian changelog.
patch-debian-changelog:
	echo Found PKG_VERSION=$(PKG_VERSION)
	if [ "$(PKG_VERSION)" != "" ]; then \
	  NEW_VERSION=$(PKG_VERSION); \
	else \
	  OLD_VERSION=`cd $(SRCDIR) && dpkg-parsechangelog -S Version` && \
	  echo Found OLD_VERSION=$${OLD_VERSION} && \
	  if dpkg --compare-versions "$${OLD_VERSION}" lt $(CBMC_VERSION) ; then \
	    NEW_VERSION=$(CBMC_VERSION)-1 ; \
	  else \
	    MINOR=`echo $${OLD_VERSION} | cut -f2 -d- | cut -f1 -d. | cut -f1 -d~` && \
	    echo Found MINOR=$${MINOR} && \
	    NEW_VERSION=$(CBMC_VERSION)-`expr $${MINOR} + 1` ; \
	  fi  \
        fi && \
	echo Found NEW_VERSION=$${NEW_VERSION} && \
	NEW_VERSION=`echo $${NEW_VERSION} | cut -f1 -d~` && \
	echo Updated NEW_VERSION=$${NEW_VERSION} && \
	mv $(SRCDIR)/debian/changelog $(SRCDIR)/debian/changelog.orig && \
	cp changelog $(SRCDIR)/debian/changelog && \
	sed -i "s/#VERSION#/$${NEW_VERSION}~$(PKG_OS)/" $(SRCDIR)/debian/changelog
	sed -i "s/#DATE#/`date -R`/" $(SRCDIR)/debian/changelog
	# Use "unstable" for Debian distribution; use Ubunu code name for Ubuntu
	if [[ `lsb_release -d` == *Ubuntu* ]]; then \
	  sed -i "s/unstable/$(PKG_OS)/" $(SRCDIR)/debian/changelog; \
        fi
	cat $(SRCDIR)/debian/changelog.orig >> $(SRCDIR)/debian/changelog
	$(RM) $(SRCDIR)/debian/changelog.orig

# Patch the debian control files.
# In particular, install cbmc-latest into /usr/local/cbmc-latest/bin and
# use locally-installed versions of debhelper and maven plug-in.
patch-debian-files:
ifeq ($(STABLE),)
	# Install cbmc-latest in /usr/local/cbmc-latest/bin (cbmc in /usr/bin)
	sed -i "s/^Package: cbmc.*/Package: $(PKG_NAME)/" $(SRCDIR)/debian/control
	sed -i "s#usr/bin#usr/local/$(PKG_NAME)/bin#g" $(SRCDIR)/debian/dirs
	sed -i "s#usr/bin#usr/local/$(PKG_NAME)/bin#g" $(SRCDIR)/debian/install
	sed -i "s#usr/bin#usr/local/$(PKG_NAME)/bin#g" $(SRCDIR)/debian/links
	echo "override_dh_usrlocal:" >> $(SRCDIR)/debian/rules
	echo "\ttrue" >> $(SRCDIR)/debian/rules
	echo "override_dh_dwz:" >> $(SRCDIR)/debian/rules
	echo "\ttrue" >> $(SRCDIR)/debian/rules
	$(RM) $(SRCDIR)/debian/manpages
	sed -i "/share\/man\/man1/d" $(SRCDIR)/debian/links
endif
	# Patch debhelper version
	DEBHELPER_VERSION=`dpkg -l debhelper | tail -n1 | awk '{print $$3}' | cut -f1 -d.` && \
	echo Found debhelper version $$DEBHELPER_VERSION && \
	echo $$DEBHELPER_VERSION > $(SRCDIR)/debian/compat && \
	if [ $$DEBHELPER_VERSION -lt 10 ] ; then \
	  sed -i 's/^\tdh $$@/\tdh $$@ --parallel/' $(SRCDIR)/debian/rules ; \
	fi
	sed -i "s/debhelper-compat *([<>=]* *[0-9]*),//" $(SRCDIR)/debian/control

# Update the debian path files.
# Changes in the source code may cause old patches to apply only with
# fuzz, and Debian package building does not allow fuzz.
patch-debian-patches: $(SRCDIR)/debian

	# Repair the maven patch on xenial: Add back the version number the patch deletes
	if [ "$(PKG_OS)" = "xenial" ] ; then \
	  sed -i "s/@@ -32,7 +32,6 @@/@@ -32,7 +32,7 @@/" $(SRCDIR)/debian/patches/maven* && \
	  sed -i "/^-[[:space:]]*<version>.*<\/version>/ a + <version>VERSION<\/version>" \
	    $(SRCDIR)/debian/patches/maven* ; \
	fi

	# Repair the maven patch: update the version number
	PLUGIN_VERSION=`dpkg -l libmaven-compiler-plugin-java | tail -n1 | awk '{print $$3}' | cut -f1 -d-` && \
	sed -i "s/^\(+[[:space:]]*<version>\).*<\/version>/\1$$PLUGIN_VERSION<\/version>/" \
	  $(SRCDIR)/debian/patches/maven*

	# Add a surefire patch to supply a version number
	cp surefire $(SRCDIR)/debian/patches
	echo "surefire" >> $(SRCDIR)/debian/patches/series
	SUREFIRE_VERSION=`dpkg -l libsurefire-java | tail -n1 | awk '{print $$3}' | cut -f1 -d-` && \
	sed -i "s/<version>SUREFIRE<\/version>/<version>$$SUREFIRE_VERSION<\/version>/" \
	  $(SRCDIR)/debian/patches/surefire

	# Patch 64bit_regression_tests patch
	cd $(SRCDIR)/debian/patches && patch < ../../../64bit_regression_tests.patch

	# Refresh all patches with quilt
	sudo apt-get -y install quilt
	cd $(SRCDIR) && export QUILT_PATCHES=debian/patches && \
		while quilt push; do quilt refresh; done && quilt pop -a
	$(RM) $(SRCDIR)/debian/patches/*~

# Patch the debian rules to build cbmc concurrently.
# See also the --parallel option added to dh above for early debhelper versions.
# This should really become part of the standard Debian build rules.
patch-debian-concurrency:
	sed -i '11s/^$$/parallel = $$(patsubst parallel=\%,\%,$$(filter parallel=\%,$$(DEB_BUILD_OPTIONS)))/' \
	  $(SRCDIR)/debian/rules
	sed -i 's/$$(MAKE)/$$(MAKE) -j$$(parallel)/' $(SRCDIR)/debian/rules

#
# End Assemble the debian directory
################################################################

build: $(SRCDIR) $(SRCDIR)/debian $(SRCDIR)/java-models-library
	sudo apt-get -y install \
	  debhelper minisat zlib1g-dev flex bison default-jdk-headless \
	  maven maven-repo-helper maven-debian-helper \
	  libmaven-compiler-plugin-java \
	  gdb
	$(MAKE) patch-debian-patches
	$(MAKE) patch-debian-changelog
	$(MAKE) patch-debian-files
	$(MAKE) patch-debian-concurrency
	cd $(SRCDIR) && dpkg-buildpackage -b -Jauto -uc -d
	# upload new artifacts

clean:
	$(RM) -r $(SRCDIR)
	$(RM) $(CBMC_NAME)_$(CBMC_VERSION).orig.tar.gz
	$(RM) $(CBMC_NAME)_$(CBMC_VERSION).orig-java-models-library.tar.gz

.PHONY: default build clean
.PHONY: patch-debian-changelog patch-debian-files patch-debian-concurrency
.PHONY: patch-debian-patches
