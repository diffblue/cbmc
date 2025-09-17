#!/usr/bin/env bash

set -e

symtab2gb_exe=$1
cbmc_exe=$2
source="${@: -1}"
goto_binary="$source.gb"

args=${*:3:$#-3}
if [[ "$args" == *" _ "* ]]
then
  args_symtab="${args%%" _ "*}"
  args_cbmc="${args#*" _ "}"
elif [[ "$args" == "_ "* ]]
then
  args_symtab=""
  args_cbmc="${args#"_ "}"
else
  args_symtab=$args
  args_cbmc=""
fi

$symtab2gb_exe "$source" ${args_symtab} --out "$goto_binary"
$cbmc_exe ${args_cbmc} "$goto_binary"
