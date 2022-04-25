#!/bin/bash

set -e

goto_cc=$1
goto_instrument=$2

sources=${*:$#}
args=${*:3:$#-3}

set -- $sources
target=${*:$#}
target=${target%.c}

if [[ `basename "${goto_cc}"` == "goto-cl" || `basename "${goto_cc}"` == "goto-cl.exe" ]]; then
  $goto_cc ${sources} "/Fe${target}.gb"
else
  $goto_cc -o ${target}.gb ${sources}
fi

echo DOING: $goto_instrument ${args} "${target}.gb"

$goto_instrument ${args} "${target}.gb"
