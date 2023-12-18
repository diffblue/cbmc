#!/usr/bin/env bash

set -e

memory_analyzer=$1
goto_gcc=$2

cmd=${*:$#}
name=$(echo $cmd | cut -d ' ' -f 1)
args=$(echo $cmd | cut -d ' ' -f 2-)

name=${name%.gb}
opts=${*:3:$#-3}

bit_width=`$memory_analyzer -h | grep -- -bit | sed 's/-bit.*//' | sed 's/.* //'`
if [[ "$bit_width" != "64" ]] && [[ $(uname -m) = "x86_64" ]]; then
  $goto_gcc -g -m32 -std=c11 -o "${name}.gb" "${name}.c"
else
  $goto_gcc -g -std=c11 -o "${name}.gb" "${name}.c"
fi
$memory_analyzer $opts "${name}.gb" $args
