#!/bin/bash

MEMORY_ANALYZER="../../../src/memory-analyzer/memory-analyzer"

set -e

NAME=${*:$#}
NAME=${NAME%.exe}

../../../src/goto-cc/goto-gcc -g -std=c11 -o $NAME.exe $NAME.c
$MEMORY_ANALYZER $@
