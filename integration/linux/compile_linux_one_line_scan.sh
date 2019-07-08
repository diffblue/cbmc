#!/bin/bash
#
# build linux with the goto-gcc compiler

# abort on failure, and show what we're doing
set -ex

# locate the script to be able to call related scripts
SCRIPT="$(readlink -e "$0")"
SCRIPTDIR="$(dirname "$SCRIPT")"

# make sure we work from the correct directory
pushd "$SCRIPTDIR"

# make tools available in PATH
export PATH=$PATH:$(readlink -e bin)

# configure build before we move on
pushd linux
make x86_64_defconfig
make kvmconfig
popd

make -C x86_64_defconfig
make -C kvmconfig

# build linux with the goto-gcc compiler
declare -i COMPILE_STATUS=0
# for now, do not consider Werror, to do so, add '--extra-cflags -Wno-error'
one-line-scan \
    --no-analysis --trunc-existing \
    -o CPROVER-linux -j $(($(nproc)/4)) -- \
    make -C linux all -j $(nproc) -k -B || COMPILE_STATUS=$?

popd

exit $COMPILE_STATUS
