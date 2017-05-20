#!/bin/bash

SRC=../../../src

GC=$SRC/goto-cc/goto-cc
GI=$SRC/goto-instrument/goto-instrument

OPTS=$1
NAME=${2%.c}

rm $NAME.gb
$GC $NAME.c --function fun -o $NAME.gb
echo $GI $OPTS $NAME.gb
$GI $OPTS $NAME.gb
