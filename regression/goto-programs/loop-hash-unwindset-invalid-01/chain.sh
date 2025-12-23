#!/usr/bin/env bash

set -e

goto_cc=$1
cbmc=$2
is_windows=$3

name="main"

if [[ "${is_windows}" == "true" ]]; then
  ${goto_cc} ${name}.c "/Fe${name}.gb"
else
  ${goto_cc} ${name}.c -o ${name}.gb
fi

# A malformed hash-based loop identifier (the hash is not a number) must be
# rejected with an "invalid loop hash" error.
${cbmc} --unwindset "main.hash_xyz:6" ${name}.gb
