#!/bin/bash

src=../../../src
goto_cc=$src/goto-cc/goto-cc
goto_instrument=$src/goto-instrument/goto-instrument
cbmc=$src/cbmc/cbmc

function usage() {
  echo "Usage: chain unwind-num test_file.c"
  exit 1
}

echo "Usage: process test_file.c to goto program"

if [ $# -eq 2 ]
then
  unwind_num=$1
  name=`echo $2 | cut -d. -f1`
  echo $unwind_num
  echo $name
else
  usage
fi

$goto_cc -o $name.gb $name.c
$goto_instrument  $name.gb ${name}-unwound.gb --unwind $unwind_num
$cbmc ${name}-unwound.gb
