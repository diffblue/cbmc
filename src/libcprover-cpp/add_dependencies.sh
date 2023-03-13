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

# We need to do the following renaming of object files because of translation
# unit name collisions which affect linking against the final artefact. For more
# details, please look at https://github.com/diffblue/cbmc/issues/7586 .

# For each library to add:
for lib in ${LIB_LIST}; do
  # We will unpack and rename all .o of dependent libraries marking them with
  # their library name to avoid clashes.
  LIBNAME=$(basename ${lib} .a)

  # Remove previous unpacked folders and create a new fresh one to work in.
  rm -rf ${LIBNAME}
  mkdir ${LIBNAME}
  cd ${LIBNAME}  

  # Unpack the library
  ${AR_COMMAND} -x ${lib}

  # Rename all object file in the library prepending "${LIBNAME}_" to avoid
  # clashes.
  for obj in *.o; do
    mv ${obj} "${LIBNAME}_${obj}"
  done

  # Move back to the working directory.
  cd ..
done

# Append all the unpacked files to the destination library
${AR_COMMAND} -rcs ${DESTINATION} **/*.o

# TODO: See if we need to do some cleanup in order to save cache space for
# Github actions runners.
