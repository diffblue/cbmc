#!/bin/bash

set -e

goto_cc=$1
goto_instrument=$2
cbmc=$3
is_windows=$4
use_dfcc=$5

name=${*:$#}
name=${name%.c}

args=${*:6:$#-6}
if [[ "$args" != *" _ "* ]]
then
  args_inst=$args
  args_cbmc=""
else
  args_inst="${args%%" _ "*}"
  args_cbmc="${args#*" _ "}"
fi

if [[ "${use_dfcc}" == "false" ]]; then
  set -- $args_inst
  args_inst=""
  while [[ $# -gt 0 ]]; do
    if [[ "x$1" == "x--dfcc" ]]; then
      shift 2
    else
      args_inst+=" $1"
      shift
    fi
  done
fi

if [[ "${is_windows}" == "true" ]]; then
  $goto_cc "${name}.c" "/Fe${name}.gb"
else
  $goto_cc -o "${name}.gb" "${name}.c"
fi

rm -f "${name}-mod.gb"
$goto_instrument ${args_inst} "${name}.gb" "${name}-mod.gb"
if [ ! -e "${name}-mod.gb" ] ; then
  cp "$name.gb" "${name}-mod.gb"
elif echo $args_inst | grep -q -- "--dump-c" ; then
  mv "${name}-mod.gb" "${name}-mod.c"

  if [[ "${is_windows}" == "true" ]]; then
    $goto_cc "${name}-mod.c" "/Fe${name}-mod.gb"
  else
    $goto_cc -o "${name}-mod.gb" "${name}-mod.c"
  fi

  rm "${name}-mod.c"
fi
$goto_instrument --show-goto-functions "${name}-mod.gb"
$cbmc "${name}-mod.gb" ${args_cbmc}
