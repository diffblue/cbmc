#!/usr/bin/env bash

set -e

cbmc=$1
goto_bmc=$2

options=${*:3:$#-3}
name=${*:$#}
base_name=${name%.c}

"${cbmc}" --export-symex-ready-goto "${base_name}.goto.symex_ready" "${name}"
"${goto_bmc}" "${base_name}.goto.symex_ready" ${options}
