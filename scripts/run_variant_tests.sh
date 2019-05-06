#!/bin/bash

set -euo pipefail

cd lib/variant
mkdir -p build
cd build
cmake -DMPARK_VARIANT_INCLUDE_TESTS="mpark" -DCMAKE_CXX_FLAGS="-std=c++11" ..
cmake --build . -- $@
ctest --output-on-failure
