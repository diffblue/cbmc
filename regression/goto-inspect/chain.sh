#!/usr/bin/env bash

set -e

# A test instruction passed to this `chain.sh` file looks like this:
# 
# build/bin/goto-cc build/bin/goto-inspect --show-goto-functions main.c
#
# This allows us to safely assume for now (as long as we're operating
# goto-inspect with one binary and one inspection option, which seems
# to be the case for now) that the option is going to be at $4.
# If this is no longer the case in the future, this script will need
# to be made significantly more sophisticated in terms of handling
# a variable number of options for the goto-inspect binary.

goto_cc_exe=$1
goto_inspect_exe=$2
is_windows=$3

name=${*:$#}
name=${name%.c}

# We need to dispatch to the appropriate platform executable because
# they accept different options.
if [[ "${is_windows}" == "true" ]]; then
  $goto_cc_exe "${name}.c" "/Fe${name}.gb"
else
  $goto_cc_exe -o "${name}.gb" "${name}.c"
fi

$goto_inspect_exe $4 "${name}.gb" 
