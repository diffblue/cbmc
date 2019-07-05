#!/bin/bash

set -e

memory_analyzer=$1
goto_gcc=$2

cmd=${*:$#}
name=$(echo $cmd | cut -d ' ' -f 1)
args=$(echo $cmd | cut -d ' ' -f 2-)

name=${name%.gb}
opts=${*:3:$#-3}

$goto_gcc -g -std=c11 -o "${name}.gb" "${name}.c"
$memory_analyzer $opts "${name}.gb" $args
