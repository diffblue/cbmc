#!/bin/bash

src_dir=../../../src

goto_analyzer=$src_dir/goto-analyzer/goto-analyzer

options=$1
file_name=${2%.c}

echo options: $options
echo file name : $file_name

$goto_analyzer $file_name.c $options --simplify $file_name_simp.out
$goto_analyzer $file_name_simp.out --show-goto-functions
