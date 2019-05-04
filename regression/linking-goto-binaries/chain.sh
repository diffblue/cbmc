#!/bin/bash

set -e

goto_cc=$1
cbmc=$2
is_windows=$3
entry_point='generated_entry_function'

main=${*:$#}
main=${main%.c}
args=${*:4:$#-4}
next=${args%.c}

if [[ "${is_windows}" == "true" ]]; then
  $goto_cc "${main}.c"
  $goto_cc "${next}.c"
  mv "${main}.exe" "${main}.gb"
  mv "${next}.exe" "${next}.gb"
else
  $goto_cc -o "${main}.gb" "${main}.c"
  $goto_cc -o "${next}.gb" "${next}.c"
fi

$cbmc "${main}.gb" "${next}.gb"
