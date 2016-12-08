#!/bin/bash

SRC=../../../src

GC=$SRC/goto-cc/goto-cc
CBMC=$SRC/cbmc/cbmc

OPTS=$1
NAME=${2%.c}

$GC $NAME.c -o $NAME.gb
$CBMC $NAME.gb $OPTS
