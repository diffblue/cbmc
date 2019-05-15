#!/bin/bash
symtab2gb_exe=$1
cbmc_exe=$2

$symtab2gb_exe "${@:3}"
$cbmc_exe a.out
