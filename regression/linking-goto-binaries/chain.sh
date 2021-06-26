#!/bin/bash

set -e

goto_cc=$1
cbmc=$2
is_windows=$3

main=${*:$#}
main=${main%.c}
args=${*:4:$#-4}
next=${args%.c}

if [[ "${is_windows}" == "true" ]]; then
  $goto_cc /c "${main}.c" "/Fo${main}.gb"
  $goto_cc /c "${next}.c" "/Fo${next}.gb"
  $goto_cc "${main}.gb" "${next}.gb" "/Fefinal.gb"
else
  $goto_cc -c -o "${main}.gb" "${main}.c"
  $goto_cc -c -o "${next}.gb" "${next}.c"
  $goto_cc "${main}.gb" "${next}.gb" -o "final.gb"
fi

$cbmc "final.gb"
