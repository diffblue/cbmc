#!/bin/bash

set -e

symtab2gb_exe=$1
cbmc_exe=$2
source="${@: -1}"
goto_binary="$source.gb"
cbmc_desc_arguments="${@:3:$#-3}"

$symtab2gb_exe "$source" --out "$goto_binary"
$cbmc_exe $cbmc_desc_arguments "$goto_binary"
