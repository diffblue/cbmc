#!/bin/sh
set -e
make -C src minisat2-download
make -C src  'CXX=${COMPILER}' 'CXXFLAGS=${SAN_FLAGS} -O2 -g ${EXTRA_CXXFLAGS}' -j2 all clobber.dir memory-models.dir musketeer.dir
