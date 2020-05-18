VERSION?=5.12

PKGDIR?=cbmc-latest
BLDDIR?=build
PACKAGE_NAME?=cbmc_${VERSION}_amd64.deb
PREFIX?=/usr/local/${PKGDIR}

################################################################
# Force SCRIPT_DIR to be explicitly set on command line
# SCRIPT_DIR?=.

default: ${PACKAGE_NAME}

# Install bison, flex, and ninja
dependencies:
	sudo apt-get install bison flex ninja-build

# Build CBMC
${BLDDIR}/bin/cbmc: dependencies
	cmake -S. -B${BLDDIR} -GNinja
	cmake --build ${BLDDIR}

# Install CBMC
${PKGDIR}: ${BLDDIR}/bin/cbmc
	mkdir -p ${PKGDIR}${PREFIX}/bin
	cp ${BLDDIR}/bin/cbmc ${PKGDIR}${PREFIX}/bin
	cp ${BLDDIR}/bin/goto-analyzer ${PKGDIR}${PREFIX}/bin
	cp ${BLDDIR}/bin/goto-cc ${PKGDIR}${PREFIX}/bin
	cp ${BLDDIR}/bin/goto-diff ${PKGDIR}${PREFIX}/bin
	cp ${BLDDIR}/bin/goto-gcc ${PKGDIR}${PREFIX}/bin
	cp ${BLDDIR}/bin/goto-harness ${PKGDIR}${PREFIX}/bin
	cp ${BLDDIR}/bin/goto-instrument ${PKGDIR}${PREFIX}/bin
	cp ${BLDDIR}/bin/goto-ld ${PKGDIR}${PREFIX}/bin
	cp ${BLDDIR}/bin/janalyzer ${PKGDIR}${PREFIX}/bin
	cp ${BLDDIR}/bin/java-unit ${PKGDIR}${PREFIX}/bin
	cp ${BLDDIR}/bin/jbmc ${PKGDIR}${PREFIX}/bin
	cp ${BLDDIR}/bin/jdiff ${PKGDIR}${PREFIX}/bin

	mkdir -p ${PKGDIR}${PREFIX}/share/man/man1
	cp doc/man/cbmc.1 ${PKGDIR}${PREFIX}/share/man/man1

# Package CBMC
${PACKAGE_NAME}: ${PKGDIR}
	@if [ -z "${SCRIPT_DIR}" ]; then \
	  echo "ERROR: SCRIPT_DIR not set"; \
	  exit 1; \
	fi
	mkdir -p ${PKGDIR}/DEBIAN
	set -- `du -ks ${PKGDIR}`
	SIZE=$1
	cat ${SCRIPT_DIR}/control | sed "s/VERSION/${VERSION}/" | sed "s/SIZE/${SIZE}/" > ${PKGDIR}/DEBIAN/control

	dpkg-deb --build ${PKGDIR} ${PACKAGE_NAME}

# Clean up everything but the ${BLDDIR}
clean:
	$(RM) -r ${PKGDIR}
	$(RM) ${PACKAGE_NAME}
