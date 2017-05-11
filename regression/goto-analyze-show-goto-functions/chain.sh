#!/bin/bash

set -e

SRC=../../../src
GA=$SRC/goto-analyzer/goto-analyzer

if [ -a $1_simplified.gb ]
  then
    rm $1_simplified.gb
fi
$GA $1 --simplify $1_simplified.gb --variable --arrays --structs --pointers
$GA $1_simplified.gb --show-goto-functions