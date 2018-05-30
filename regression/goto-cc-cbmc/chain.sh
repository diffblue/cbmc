#!/usr/bin/env bash

goto_cc=$1
cbmc=$2
is_windows=$3

options=${*:4:$#-4}
name=${*:$#}
base_name=${name%.c}
base_name=${base_name%.cpp}

if [[ "${is_windows}" == "true" ]]; then
  "${goto_cc}" "${name}"
  mv "${base_name}.exe" "${base_name}.gb"
else
  "${goto_cc}" "${name}" -o "${base_name}.gb"
fi

"${cbmc}" "${base_name}.gb" ${options}
