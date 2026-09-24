#!/usr/bin/env bash

set -e

goto_cc=$1
cbmc=$2
is_windows=$3

if [[ "${is_windows}" == "true" ]]; then
  ${goto_cc} original.c "/Feoriginal.gb"
  ${goto_cc} shifted.c "/Feshifted.gb"
else
  ${goto_cc} original.c -o original.gb
  ${goto_cc} shifted.c -o shifted.gb
fi

# Extract hashes from both versions
hash1=$(${cbmc} --show-loops original.gb | grep -o 'hash main\.hash_[0-9]*' | sed 's/hash main\.hash_//' | sort -n)
hash2=$(${cbmc} --show-loops shifted.gb | grep -o 'hash main\.hash_[0-9]*' | sed 's/hash main\.hash_//' | sort -n)

# Compare - should be identical
if [ "$hash1" == "$hash2" ]; then
  echo "STABLE: Hashes match"
  echo "$hash1"
else
  echo "UNSTABLE: Hashes differ"
  echo "Original: $hash1"
  echo "Shifted: $hash2"
  exit 1
fi
