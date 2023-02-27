#!/usr/bin/env sh

set -e

AR_COMMAND=$1
shift
DESTINATION=$1
shift
LIB_LIST=$@

for lib in ${LIB_LIST}; do
  ${AR_COMMAND} -x ${lib}
done

${AR_COMMAND} -rcs ${DESTINATION} *.o
