#!/bin/bash

set -e

src=../../../src
goto_cc=$src/goto-cc/goto-cc
goto_instrument=$src/goto-instrument/goto-instrument
cbmc=$src/cbmc/cbmc

name=${@:$#}
name=${name%.c}

args=${@:1:$#-1}

if [ -f $name.c ] ; then
  $goto_cc -o $name.gb $name.c
# $goto_instrument --show-goto-functions $name.gb
  $goto_instrument $args $name.gb ${name}-mod.gb
  if [ ! -e ${name}-mod.gb ] ; then
    cp $name.gb ${name}-mod.gb
  elif echo "$args" | grep -q -- "--dump-c" ; then
    mv ${name}-mod.gb ${name}-mod.c
    $goto_cc ${name}-mod.c -o ${name}-mod.gb
    rm ${name}-mod.c
  fi
$goto_instrument --show-goto-functions ${name}-mod.gb
$cbmc ${name}-mod.gb
else
  $cbmc $name
fi

