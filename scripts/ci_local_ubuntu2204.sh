#!/bin/bash
# Build and test CBMC in Ubuntu 22.04 Docker container (GCC 11)
# Usage: ./scripts/ci_local_ubuntu2204.sh [test_args...]
# Examples:
#   ./scripts/ci_local_ubuntu2204.sh                    # run cbmc-cpp CORE
#   ./scripts/ci_local_ubuntu2204.sh cpp11_vector_size  # run single test
#   ./scripts/ci_local_ubuntu2204.sh --suite cpp        # run cpp suite

set -e
REPO_DIR="$(cd "$(dirname "$0")/.." && pwd)"
ARGS="${*:-}"

sudo docker run --rm \
  -v "$REPO_DIR:/cbmc:ro" \
  ubuntu:22.04 \
  bash -c "
set -e
export DEBIAN_FRONTEND=noninteractive
apt-get update -qq >/dev/null 2>&1
apt-get install -y --no-install-recommends \
  g++ gcc flex bison cmake make perl git patch ca-certificates >/dev/null 2>&1

cp -a /cbmc /tmp/cbmc
cd /tmp/cbmc
git config --global --add safe.directory '*'
git submodule update --init --recursive --depth 1 -- src 2>/dev/null

rm -rf build && mkdir build && cd build
cmake .. -DWITH_JBMC=OFF 2>&1 | tail -1
cmake --build . --target cbmc --target goto-cc -- -j\$(nproc) 2>&1 | tail -1

if [ '$ARGS' = '--suite cpp' ]; then
  cd /tmp/cbmc/regression/cpp
  perl ../test.pl -e -p -c '/tmp/cbmc/build/bin/goto-cc' -C -t 60
elif [ -n '$ARGS' ] && [ '$ARGS' != '--suite cpp' ]; then
  cd /tmp/cbmc/regression/cbmc-cpp
  perl ../test.pl -e -p -c '/tmp/cbmc/build/bin/cbmc --validate-goto-model --validate-ssa-equation' $ARGS -t 180
else
  cd /tmp/cbmc/regression/cbmc-cpp
  perl ../test.pl -e -p -c '/tmp/cbmc/build/bin/cbmc --validate-goto-model --validate-ssa-equation' -C -X libcxx -X no-validate -t 180
fi
"
