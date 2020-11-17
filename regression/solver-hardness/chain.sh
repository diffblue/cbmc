#!/bin/bash

cbmc=$1

name=${*:$#}
args=${*:2:$#-2}

$cbmc ${name} ${args}
CBMC_RETURN_CODE="$?"
jq -c . "solver_hardness.json"
exit ${CBMC_RETURN_CODE}
