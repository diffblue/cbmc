#!/bin/bash

src=../../../src
goto_cc=$src/goto-cc/goto-cc
goto_instrument=$src/goto-instrument/goto-instrument


function usage() {
  echo "Usage: chain analysis test_file.c"
  exit 1
}

name=`echo $2 | cut -d. -f1`
flag=$1

$goto_cc -o $name.o $name.c
$goto_instrument $flag $name.o

