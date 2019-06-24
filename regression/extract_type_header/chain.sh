#!/bin/bash

set -e

goto_cc=$1
goto_instrument=$2
cbmc=$3
python_script=$4
is_windows=$5

name=${*:$#}
name=${name%.c}

args=${*:6:$#-6}

if [[ "${is_windows}" == "true" ]]; then
  $goto_cc "${name}.c"
  mv "${name}.exe" "${name}.gb"
else
  $goto_cc -o "${name}.gb" "${name}.c"
fi

export PATH=$PATH:"$(pwd)../../../src/goto-instrument/"
$python_script "${name}.gb" "${name}.c" "header.h"
cat "header.h"
rm -f "header.h"
