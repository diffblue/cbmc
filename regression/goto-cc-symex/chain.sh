#!/bin/bash

src=../../../src

gc=$src/goto-cc/goto-cc
symex=$src/symex/symex

options=$1
name=${2%.c}

$gc $name.c -o $name.gb
$symex $name.gb $options
