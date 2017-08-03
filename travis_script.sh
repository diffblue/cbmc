#!/bin/sh
set -e
make -C unit 'CXX=${COMPILER}' 'CXXFLAGS=${SAN_FLAGS} -O2 -g ${EXTRA_CXXFLAGS}' -j2
make -C unit test
if [ -e bin/gcc ] ; then export PATH=$PWD/bin:$PATH ; fi ; env UBSAN_OPTIONS=print_stacktrace=1 make -C regression test
