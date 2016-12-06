#!/bin/bash

src=../../../src
goto_cc=$src/goto-cc/goto-cc
goto_instrument=$src/goto-instrument/goto-instrument
cbmc=$src/cbmc/cbmc

name=${@:$#}
name=${name%.c}

args=${@:1:$#-1}

$goto_cc -o $name.gb $name.c
$goto_instrument --show-goto-functions $name.gb
$goto_instrument $args $name.gb ${name}-unwound.gb
$goto_instrument --show-goto-functions ${name}-unwound.gb
$cbmc ${name}-unwound.gb

