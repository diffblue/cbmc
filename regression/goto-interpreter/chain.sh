#!/usr/bin/env bash

set -e

goto_cc=$1
goto_instrument=$2
is_windows=$3

options=${*:4:$#-4}
name=${*:$#}
base_name=${name%.c}

if [[ "${is_windows}" == "true" ]]; then
  "${goto_cc}" "${name}" "/Fe${base_name}.gb"
else
  "${goto_cc}" "${name}" -o "${base_name}.gb"
fi

echo ${options} | tr , '\n' | "${goto_instrument}" --interpreter "${base_name}.gb"
