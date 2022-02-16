#!/usr/bin/env bash
set -e

goto_cc=$1
is_windows=$2

if [[ "${is_windows}" == "true" ]]; then
  ${goto_cc} "/c" "/Foproject.gb" --export-file-local-symbols project.c
  ${goto_cc} "/c" "/Foproof.gb" --export-file-local-symbols proof.c
  ${goto_cc} "/Fetest.gb" project.gb proof.gb
else
  ${goto_cc} -o project.gb --export-file-local-symbols project.c
  ${goto_cc} -o proof.gb --export-file-local-symbols proof.c
  ${goto_cc} -o test.gb project.gb proof.gb
fi
