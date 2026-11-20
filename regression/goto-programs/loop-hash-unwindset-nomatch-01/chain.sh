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

# A well-formed but non-matching hash must be reported as not matching any
# loop and then ignored, so verification still succeeds.
${cbmc} --unwindset "main.hash_123:6" ${name}.gb
