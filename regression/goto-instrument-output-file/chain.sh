#!/usr/bin/env bash

set -e

goto_cc=$1
goto_instrument=$2
is_windows=$3

name=${*:$#}
name=${name%.c}

args=${*:4:$#-4}

rm -f "${name}.gb"
if [[ "${is_windows}" == "true" ]]; then
  "$goto_cc" "${name}.c" "/Fe${name}.gb"
else
  "$goto_cc" -o "${name}.gb" "${name}.c"
fi

# Deliberately invoke goto-instrument with a single positional argument (the
# input goto binary only, no output file) to exercise the early output-file
# validation in goto_instrument_parse_optionst::doit().
"$goto_instrument" ${args} "${name}.gb"
