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

# Extract the hash from --show-loops output
hash=$(${cbmc} --show-loops ${name}.gb | grep -o 'hash main\.hash_[0-9]*' | sed 's/hash //')

# The loop needs 6 unwindings to verify, but --unwind 2 would be
# insufficient. The hash-based unwindset overrides the global limit.
${cbmc} --unwind 2 --unwindset "${hash}:6" ${name}.gb
