#!/bin/bash

SRC=../../../src

GC=$SRC/goto-cc/goto-cc
GI=$SRC/goto-instrument/goto-instrument

OPTS=$1
NAME=${2%.c}

$GC $NAME.c -o $NAME.gb
$GI $OPTS $NAME.gb
