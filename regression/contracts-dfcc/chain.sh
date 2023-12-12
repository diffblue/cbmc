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

dfcc_suffix=""
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
else
  dfcc_suffix="dfcc"
fi

if [[ "${is_windows}" == "true" ]]; then
  $goto_cc "${name}.c" "/Fe${name}${dfcc_suffix}.gb"
else
  $goto_cc -o "${name}${dfcc_suffix}.gb" "${name}.c"
fi

rm -f "${name}${dfcc_suffix}-mod.gb"
$goto_instrument ${args_inst} "${name}${dfcc_suffix}.gb" "${name}${dfcc_suffix}-mod.gb"
if [ ! -e "${name}${dfcc_suffix}-mod.gb" ] ; then
  cp "${name}${dfcc_suffix}.gb" "${name}${dfcc_suffix}-mod.gb"
elif echo $args_inst | grep -q -- "--dump-c" ; then
  mv "${name}${dfcc_suffix}-mod.gb" "${name}${dfcc_suffix}-mod.c"

  if [[ "${is_windows}" == "true" ]]; then
    $goto_cc "${name}${dfcc_suffix}-mod.c" "/Fe${name}${dfcc_suffix}-mod.gb"
  else
    $goto_cc -o "${name}${dfcc_suffix}-mod.gb" "${name}${dfcc_suffix}-mod.c"
  fi

  rm "${name}${dfcc_suffix}-mod.c"
fi
$goto_instrument --show-goto-functions "${name}${dfcc_suffix}-mod.gb"
$cbmc "${name}${dfcc_suffix}-mod.gb" ${args_cbmc}
