#!/bin/bash

set -e

memory_analyzer=$1
goto_gcc=$2
name=${*:$#}
name=${name%.gb}
args=${*:3:$#-3}

$goto_gcc -g -std=c11 -o "${name}.gb" "${name}.c"
$memory_analyzer $args "${name}.gb"
