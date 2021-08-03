#!/bin/bash

set -e

symtab2gb_exe=$1
goto_instrument_exe=$2

name=${*:$#}

args=${*:3:$#-3}

$symtab2gb_exe "${name}"
$goto_instrument_exe "${args}" a.out
