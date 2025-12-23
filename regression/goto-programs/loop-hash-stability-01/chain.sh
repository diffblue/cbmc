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

# Extract hash values from --show-loops output
${cbmc} --show-loops ${name}.gb | grep -o 'hash main\.hash_[0-9]*' | sed 's/hash main\.hash_//' | sort -n
