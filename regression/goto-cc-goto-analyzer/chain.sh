#!/bin/bash

src=../../../src

gc=$src/goto-cc/goto-cc
goto_analyzer=$src/goto-analyzer/goto-analyzer

options=$1
name=${2%.c}

$gc $name.c -o $name.gb
$goto_analyzer $name.gb $options
