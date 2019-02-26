#!/bin/bash

set -e

goto_cc=$1
goto_harness=$2
cbmc=$3
is_windows=$4
entry_point='generated_entry_function'

name=${*:$#}
name=${name%.c}
args=${*:5:$#-5}

if [[ "${is_windows}" == "true" ]]; then
  $goto_cc "${name}.c"
  mv "${name}.exe" "${name}.gb"
else
  $goto_cc -o "${name}.gb" "${name}.c"
fi

if [ -e "${name}-mod.gb" ] ; then
  rm -f "${name}-mod.gb"
fi

$goto_harness "${name}.gb" "${name}-mod.gb" --harness-function-name $entry_point ${args} 
$cbmc --function $entry_point "${name}-mod.gb" --unwind 20 --unwinding-assertions
