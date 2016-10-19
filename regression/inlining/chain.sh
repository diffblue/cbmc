#!/bin/bash

set -e

src=../../../src
goto_cc=$src/goto-cc/goto-cc
goto_instrument=$src/goto-instrument/goto-instrument
cbmc=$src/cbmc/cbmc

name=${@:$#}
name=${name%.c}

args=${@:1:$#-1}

$goto_cc -o $name.o $name.c
$goto_instrument $args $name.o $name-new.o
$goto_instrument --show-goto-functions $name-new.o
$cbmc $name-new.o

