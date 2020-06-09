#!/usr/bin/env bash

goto_cc=$1
cbmc=$2
goto_instrument=$3
is_windows=$4

name=${*:$#}
base_name=${name%.c}
modified_name=${base_name}.modified.c

if [[ "${is_windows}" == "true" ]]; then
  "${goto_cc}" "${name}"
  mv "${base_name}.exe" "${base_name}.gb"
else
  "${goto_cc}" "${name}" -o "${base_name}.gb"
fi

"${goto_instrument}" "${base_name}.gb" --dump-c "${modified_name}"

"${cbmc}" "${modified_name}"
