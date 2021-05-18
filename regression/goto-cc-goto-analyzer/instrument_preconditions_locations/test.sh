#!/usr/bin/env bash
set -e

goto_cc=$1
is_windows=$2

if [[ "${is_windows}" == "true" ]]; then
  ${goto_cc}  --export-file-local-symbols  simple.c 
  mv simple.exe simple.gb
  ${goto_cc}  --export-file-local-symbols  s2n_hash_inlined.c
  mv s2n_hash_inlined.exe s2n_hash_inlined.gb
  ${goto_cc}  --function s2n_hash_free_harness simple.gb s2n_hash_inlined.gb
  mv simple.exe test.gb
else
  ${goto_cc}  --export-file-local-symbols  simple.c -o simple.gb
  ${goto_cc}  --export-file-local-symbols  s2n_hash_inlined.c -o s2n_hash_inlined.gb
  ${goto_cc}  --function s2n_hash_free_harness simple.gb s2n_hash_inlined.gb -o test.gb
fi
