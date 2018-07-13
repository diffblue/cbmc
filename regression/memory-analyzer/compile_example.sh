#!/bin/bash

MEMORYANALYZER="../../../src/memory-analyzer/memory-analyzer"

set -e

NAME=${5%.exe}

../../../src/goto-cc/goto-gcc -g -std=c11 -o $NAME.exe $NAME.c
$MEMORYANALYZER $@
