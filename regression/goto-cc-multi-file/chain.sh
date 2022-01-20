#!/usr/bin/env bash

set -e

goto_cc=$1
cbmc=$2
is_windows=$3

args=${*:4:$#-4}
name=${*:$#}
name=${name%.c}

if [[ "${is_windows}" == "true" ]]; then
  ${goto_cc} ${name}.c ${args} "/Fe${name}.gb"
else
  ${goto_cc} ${name}.c ${args} -o ${name}.gb
fi

${cbmc} --show-goto-functions ${name}.gb
