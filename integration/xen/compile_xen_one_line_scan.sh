#!/bin/bash
#
# build xen with the goto-gcc compiler

# abort on failure, and show what we're doing
set -ex

# locate the script to be able to call related scripts
SCRIPT="$(readlink -e "$0")"
SCRIPTDIR="$(dirname "$SCRIPT")"

# make sure we work from the correct directory
pushd "$SCRIPTDIR"

# make tools available in PATH
export PATH=$PATH:$(readlink -e bin)

# build xen with the goto-gcc compiler
declare -i COMPILE_STATUS=0
one-line-scan \
    --no-analysis --trunc-existing \
    --extra-cflags -Wno-error \
    -o CPROVER-xen -j $(($(nproc)/4)) -- \
    make -C xen xen -j $(nproc) -k -B || COMPILE_STATUS=$?

popd

exit $COMPILE_STATUS
