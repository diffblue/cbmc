#!/usr/bin/env bash
#
# This particular file and chain.sh make sure that a particular
# file is passed twice to goto-cc, causing a crash under some
# specific name mangling configuration.
#
# Author: Fotis Koutoulakis fotis.koutoulakis@diffblue.com

set -e # cause the script to immediately exit when it errors

goto_cc=$1
is_windows=$2

# collect compilation files
PROBLEM_SRC="test.c"
MAIN_SRC="main.c"

echo "source files are ${SRC}"

MAIN_OUTFILE="main.gb"
PROBLEM_OUTFILE="test.gb"

# first drive: compile the problematic file into a gb
if [[ "${is_windows}" == "true" ]]; then
  "${goto_cc}" --export-file-local-symbols "${PROBLEM_SRC}" "/Fe${PROBLEM_OUTFILE}"
else
  "${goto_cc}" --export-file-local-symbols "${PROBLEM_SRC}" -o "${PROBLEM_OUTFILE}"
fi

# second drive: compile and link the main source, problematic source and problematic
# binary - note: the double inclusion of a similar artifact (source and binary) is
# by design, to test a regression in goto-cc
"${goto_cc}" --export-file-local-symbols "${PROBLEM_SRC}" "${MAIN_SRC}" "${PROBLEM_OUTFILE}"
