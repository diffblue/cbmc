#!/bin/bash

# Fail on errors
# set -e # not for now

# Show steps we execute
set -x

# This script needs to operate in the root directory of the CBMC repository
SCRIPT=$(readlink -e "$0")
readonly SCRIPT
SCRIPTDIR=$(dirname "$SCRIPT")
readonly SCRIPTDIR
cd "$SCRIPTDIR/../.."

# Build CBMC tools
make -C src minisat2-download
make -C src CXX='ccache /usr/bin/g++' cbmc.dir goto-cc.dir goto-diff.dir -j$(nproc)

# Get one-line-scan, if we do not have it already
[ -d one-line-scan ] || git clone https://github.com/awslabs/one-line-scan.git one-line-scan

# Get Linux v5.10, if we do not have it already
[ -d linux_5_10 ] || git clone -b v5.10 --depth=1 https://github.com/torvalds/linux/ linux_5_10

# Prepare compile a part of the kernel with CBMC via one-line-scan
ln -s goto-cc src/goto-cc/goto-ld
ln -s goto-cc src/goto-cc/goto-as
ln -s goto-cc src/goto-cc/goto-g++


configure_linux ()
{
  pushd linux_5_10

  cat > kvm-config <<EOF
CONFIG_64BIT=y
CONFIG_X86_64=y
CONFIG_HIGH_RES_TIMERS=y
CONFIG_MULTIUSER=y
CONFIG_NET=y
CONFIG_VIRTUALIZATION=y
CONFIG_HYPERVISOR_GUEST=y
CONFIG_PARAVIRT=y
CONFIG_KVM_GUEST=y
CONFIG_KVM=y
CONFIG_KVM_INTEL=y
CONFIG_KVM_AMD=y
EOF
  # use the configuration from the generated file
  export KCONFIG_ALLCONFIG=kvm-config

  # ... and use it during configuration
  make allnoconfig
  popd
}

# Configure kernel, and compile all of it
configure_linux
make -C linux_5_10 bzImage -j $(nproc)

# Clean files we want to be able to re-compile
find linux_5_10/arch/x86/kvm/ -name "*.o" -delete

# Compile Linux with CBMC via one-line-scan, and check for goto-cc section
# Re-Compile with goto-cc, and measure disk space
declare -i STATUS=0
du -h --max-depth=1
one-line-scan/one-line-scan \
    --add-to-path $(pwd)/src/cbmc --add-to-path $(pwd)/src/goto-diff --add-to-path $(pwd)/src/goto-cc \
    --cbmc \
    --no-analysis \
    --trunc-existing \
    --extra-cflags -Wno-error \
    -o CPROVER -j 5 -- \
    make -C linux_5_10 bzImage -j $(nproc) || STATUS=$?
du -h --max-depth=1

# Check for faulty input
ls CPROVER/faultyInput/* || true

# Check for produced output in the files we deleted above
objdump -h linux_5_10/arch/x86/kvm/x86.o | grep "goto-cc" || STATUS=$?

# Propagate failures
exit "$STATUS"
