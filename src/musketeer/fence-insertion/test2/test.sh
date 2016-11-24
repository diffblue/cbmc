#!/bin/bash

set -e

T='test.sh:'

prepare() {
  ./clean.sh
  cp test.c.orig test.c
}

prepare
gcc -std=c99 -Wall -o test1 test.c
echo -e $T 'Original compiled successfully.\n'

prepare
../fi.py x86 fence musk results.txt
gcc -std=c99 -Wall -o test2 test.c
echo -e $T 'Fenced compiled successfully (musketeer format).\n'

./clean.sh

