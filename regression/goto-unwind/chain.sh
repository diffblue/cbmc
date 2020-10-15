#!/bin/bash

##################################################################################################################
#
#                          goto-unwind chain.sh
#
# Arguments: goto_cc goto_unwind cbmc is_windows (goto_unwind_arg)* C-file
#
# The first 3 arguments are the paths to the goto_cc, goto_unwind and cbmc binaries to use.
# The 4th one is true/false indicating whether or not we are on windows (in
# which case goto_cc will use the cl command-line interface so the logic is slightly different).
# Any further arguments are passed on to goto-unwind, except for the last one which will be the C file
# we compile and run goto-unwind on.
#
# What actually happens here is basically:
#   goto-cc test.c -o test.gb
#   goto-unwind test.gb test-out.gb $args
#   cbmc test-out.gb
##################################################################################################################

set -e

if [[ $# < 5 ]]; then
  echo >&2 "Expected at least 5 arguments: goto-cc, goto_unwind, cbmc, is_windows and at least a C file to test"
fi
goto_cc=$1
goto_unwind=$2
cbmc=$3
is_windows=$4

name=${*:$#}

name=${name%.c}

args=${*:5:$#-5}

if [[ "${is_windows}" == "true" ]]; then
  $goto_cc "${name}.c"
  mv "${name}.exe" "${name}.gb"
else
  $goto_cc -o "${name}.gb" "${name}.c"
fi

rm -f "${name}-mod.gb"
$goto_unwind ${args} "${name}.gb" "${name}-mod.gb"
$cbmc "${name}-mod.gb"
