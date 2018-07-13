#!/bin/bash

MEMORYANALYZER="../../../src/memory-analyzer/memory-analyzer"

set -e

NAME=${5%.exe}

goto-gcc -g -o $NAME.exe $NAME.c
$MEMORYANALYZER $@
