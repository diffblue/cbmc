#!/bin/bash

set -e

goto_analyzer=$1

options=${*:2:$#-2}
name=${*:$#}
name=${name%.c}

"${goto_analyzer}" "${name}.c" ${options} --simplify "${name}.gb"
"${goto_analyzer}" "${name}.gb" --show-goto-functions
