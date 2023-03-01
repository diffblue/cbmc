#!/usr/bin/env sh

# This script adds to a static library archive file `lib<name>.a` all the object files of a set of
# other libraries it depends on.
# This script takes 3 or more arguments:
# 1. the archive command
# 2. the destination library path
# 3. a list of paths of static libraries to be added to the destination library archive

set -e

AR_COMMAND=$1
shift
DESTINATION=$1
shift
LIB_LIST=$@

# For each library to add:
for lib in ${LIB_LIST}; do
  # Unpack the library
  ${AR_COMMAND} -x ${lib}
done

# Append all the unpacked files to the destination library
${AR_COMMAND} -rcs ${DESTINATION} *.o
