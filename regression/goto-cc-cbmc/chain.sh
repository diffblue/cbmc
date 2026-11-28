#!/usr/bin/env bash

set -e

goto_cc=$1
cbmc=$2
is_windows=$3

options=${*:4:$#-4}
name=${*:$#}
base_name=${name%.c}
base_name=${base_name%.cpp}

# Options before a "_" are passed to goto-cc, the remaining ones to cbmc.
goto_cc_options=""
if [[ "${options}" == "_ "* || "${options}" == *" _ "* || "${options}" == *" _" ]]; then
  goto_cc_options="${options%%_*}"
  options="${options#*_}"
fi

if [[ "${is_windows}" == "true" ]]; then
  "${goto_cc}" ${goto_cc_options} "${name}" "/Fe${base_name}.gb"
else
  "${goto_cc}" ${goto_cc_options} "${name}" -o "${base_name}.gb"
fi

"${cbmc}" "${base_name}.gb" ${options}
