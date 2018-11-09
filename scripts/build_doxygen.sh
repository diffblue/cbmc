#!/bin/bash

DOXYGEN_VERSION=$1

if [ $# -ne 1 ]
then
  echo "Usage: build_doxygen.sh doxygen-version-number"
  exit 1
fi

mkdir -p doxygen/build \
&& wget http://ftp.stack.nl/pub/users/dimitri/doxygen-${DOXYGEN_VERSION}.src.tar.gz -O- | tar -xz --strip-components=1 --directory doxygen \
&& ( cd doxygen/build && cmake .. ) \
&& make -j4 -C doxygen/build
