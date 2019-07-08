#!/bin/bash

# abort on failure, and show what we're doing
set -ex

# locate the script to be able to call related scripts
SCRIPT="$(readlink -e "$0")"
SCRIPTDIR="$(dirname "$SCRIPT")"

DOCKERFILE=$(readlink -e "$SCRIPTDIR"/Dockerfile)

# make sure we have what we need
assert_environment()
{
    if ! command -v docker &> /dev/null
    then
        echo "error: docker not found, abort"
        exit 1
    fi

    if [ ! -r $DOCKERFILE ]
    then
        echo "error: cannot read Dockerfile $DOCKERFILE, abort"
        exit 1
    fi

    # test whether we can build the container and run a simple command
    pushd "$SCRIPTDIR"/../..
    scripts/run_in_container.sh "$DOCKERFILE" ls integration/xen
    popd
}

# get a recent copy of one-line-scan
get_one_line_scan ()
{
    rm -rf one-line-scan
    git clone https://github.com/awslabs/one-line-scan.git
}

# get a local copy of the xen repository, and jump to origin/master
get_and_update_xen ()
{
    [ -d xen ] || git clone git://xenbits.xen.org/xen.git
    pushd xen
    git fetch origin
    git checkout origin/master
    popd
}

# setup CBMC to be used in one-line-scan
setup_cbmc_in_container ()
{
    pushd "$SCRIPTDIR"/../..
    scripts/run_in_container.sh "$DOCKERFILE" make -C src minisat2-download
    scripts/run_in_container.sh "$DOCKERFILE" make -C src -j$(nproc)
    popd
}

# setup PATH to have all tools
setup_PATH ()
{
    mkdir -p bin
    pushd bin
    rm -rf ./*

    # create all links we might need
    ln -s ../../../src/goto-cc/goto-cc goto-ar
    ln -s ../../../src/goto-cc/goto-cc goto-as
    ln -s ../../../src/goto-cc/goto-cc goto-diff
    ln -s ../../../src/goto-cc/goto-cc goto-gcc
    ln -s ../../../src/goto-cc/goto-cc goto-ld

    ln -s ../one-line-scan/one-line-scan one-line-scan

    # actually update the PATH variable
    export PATH=$PATH:$(readlink -e .)

    popd
}

compile_xen_in_container ()
{
    pushd "$SCRIPTDIR"/../..

    pwd

    # make sure we start fresh
    scripts/run_in_container.sh "$DOCKERFILE" make -C integration/xen/xen clean

    # build xen with the goto-gcc compiler
    declare -i COMPILE_STATUS=0
    scripts/run_in_container.sh "$DOCKERFILE" integration/xen/compile_xen_one_line_scan.sh || COMPILE_STATUS=$?

    popd

    return $COMPILE_STATUS
}

# steps to execute

assert_environment

get_one_line_scan

get_and_update_xen

setup_cbmc_in_container

# setup path
setup_PATH

# compile xen
declare -i COMPILE_STATUS
COMPILE_STATUS=0
compile_xen_in_container || COMPILE_STATUS=$?

# evaluate
if [ "$COMPILE_STATUS" -eq 0 ]
then
  echo "SUCCESS: Compilation of Xen succeeded"
else
  echo -n "FAILED: Compilation of Xen failed."
  echo -n " The build log can be found in"
  echo " CPROVER-xen/build.log"
fi

exit $COMPILE_STATUS
