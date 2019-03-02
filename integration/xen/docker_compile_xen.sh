#/bin/bash

set -e

cd /tmp/cbmc/src

make minisat2-download
make -j$(nproc)

mkdir /tmp/xen_compilation
cd /tmp/xen_compilation
ln -s /tmp/cbmc/src/goto-cc/goto-cc goto-ld
ln -s /tmp/cbmc/src/goto-cc/goto-cc goto-gcc
ln -s /tmp/cbmc/src/goto-cc/goto-cc goto-diff

git clone https://github.com/awslabs/one-line-scan.git

git clone git://xenbits.xen.org/xen.git

export PATH=$(pwd)/one-line-scan/configuration:$PATH
export PATH=$(pwd):$PATH

cd xen
if one-line-scan \
  --no-analysis --trunc-existing \
  --extra-cflags -Wno-error \
  -o CPROVER -j $(($(nproc)/4)) -- make xen -j$(nproc)
then
  echo "SUCCESS: Compilation of Xen succeeded"
else
  echo -n "FAILED: Compilation of Xen failed."
  echo -n " The build log can be found in"
  echo " /tmp/xen_compilation/xen/CPROVER/build.log"
fi
