#!/bin/bash

src=../../../src
goto_cc=$src/goto-cc/goto-cc
goto_instrument=$src/goto-instrument/goto-instrument

name=${@:$#}
name=${name%.c}

args=${@:1:$#-1}

$goto_cc -o $name.gb $name.c
$goto_instrument $args $name.gb

