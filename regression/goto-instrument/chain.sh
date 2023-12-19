#!/usr/bin/env bash

set -e

goto_cc=$1
goto_instrument=$2
cbmc=$3
is_windows=$4

sources=${*:$#}
args=${*:5:$#-5}

if [[ "$args" != *" _ "* ]]
then
  args_inst=$args
  args_cbmc=""
else
  args_inst="${args%%" _ "*}"
  args_cbmc="${args#*" _ "}"
fi

set -- $sources
target=${*:$#}
target=${target%.c}

if [[ "${is_windows}" == "true" ]]; then
  $goto_cc ${sources} "/Fe${target}.gb"
else
  $goto_cc -o ${target}.gb ${sources}
fi

rm -f "${target}-mod.gb"
$goto_instrument ${args_inst} "${target}.gb" "${target}-mod.gb"
if [ ! -e "${target}-mod.gb" ] ; then
  cp "${target}.gb" "${target}-mod.gb"
elif echo $args | grep -q -- "--dump-c-type-header" ; then
  cat "${target}-mod.gb"
  mv "${target}.gb" "${target}-mod.gb"
elif echo $args | grep -q -- "--dump-c" ; then
  cat "${target}-mod.gb"
  mv "${target}-mod.gb" "${target}-mod.c"

  if [[ "${is_windows}" == "true" ]]; then
    $goto_cc "${target}-mod.c" "/Fe${target}-mod.gb"
  else
    $goto_cc -o "${target}-mod.gb" "${target}-mod.c"
  fi

  rm "${target}-mod.c"
fi
$goto_instrument --show-goto-functions "${target}-mod.gb"
$cbmc ${args_cbmc}  "${target}-mod.gb"
