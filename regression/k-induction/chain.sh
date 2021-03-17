#!/bin/bash

set -e

goto_cc=$1
goto_instrument=$2
cbmc=$3
is_windows=$4

shift 4

function usage() {
  echo "Usage: chain k test_file.c"
  exit 1
}

name=`echo $2 | cut -d. -f1`
k=$1

if [[ "${is_windows}" == "true" ]]; then
  $goto_cc "${name}.c" "/Fe${name}.gb"
else
  $goto_cc -o "${name}.gb" "${name}.c"
fi


"$goto_instrument" --k-induction $k --base-case "$name.gb" "$name.base.gb"
if "$cbmc" "$name.base.gb" ; then
  echo "## Base case passes"
else
  echo "## Base case fails"
fi

"$goto_instrument" --k-induction $k --step-case "$name.gb" "$name.step.gb"
if "$cbmc" "$name.step.gb" ; then
  echo "## Step case passes"
else
  echo "## Step case fails"
fi
