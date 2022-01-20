#!/usr/bin/env bash

set -e

goto_cc=$1
goto_analyzer=$2
is_windows=$3

options=${*:4:$#-4}
name=${*:$#}
name=${name%.c}
buildgoto=${name}.sh

if test -f ${buildgoto}; then
  ./${buildgoto} ${goto_cc} ${is_windows}
else
  if [[ "${is_windows}" == "true" ]]; then
    "${goto_cc}" "${name}.c" "/Fe${name}.gb"
  else
    "${goto_cc}" "${name}.c" -o "${name}.gb"
  fi
fi

"${goto_analyzer}" "${name}.gb" ${options}
