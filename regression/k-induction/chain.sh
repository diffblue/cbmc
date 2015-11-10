#!/bin/bash

src=../../../src
goto_cc=$src/goto-cc/goto-cc
goto_instrument=$src/goto-instrument/goto-instrument
cbmc=$src/cbmc/cbmc

function usage() {
  echo "Usage: chain k test_file.c"
  exit 1
}

name=`echo $2 | cut -d. -f1`
k=$1

$goto_cc -o $name.o $name.c

$goto_instrument --k-induction $k --base-case $name.o $name.base.o
$cbmc $name.base.o
if [ $? == 0 ] ; then echo "## Base case passes" ; fi

$goto_instrument --k-induction $k --step-case $name.o $name.step.o
$cbmc $name.step.o
if [ $? == 0 ] ; then echo "## Step case passes" ; fi


