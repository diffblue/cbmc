#!/usr/bin/env bash

set -e

goto_cc=$1
goto_instrument=$2
cbmc=$3
is_windows=$4

name=${*:$#}
name=${name%.c}

args=${*:5:$#-5}
if [[ "$args" != *" _ "* ]]
then
  args_inst=$args
  args_cbmc=""
else
  args_inst="${args%%" _ "*}"
  args_cbmc="${args#*" _ "}"
fi

if [[ "${is_windows}" == "true" ]]; then
  $goto_cc "${name}.c" "/Fe${name}.gb"
else
  $goto_cc -o "${name}.gb" "${name}.c"
fi

rm -f "${name}-mod.gb"
# Several goto-instrument invocations can be chained by separating their
# arguments with " -- "; each one reads the output of the previous one.
if [[ "$args_inst" != *" -- "* ]]
then
  $goto_instrument ${args_inst} "${name}.gb" "${name}-mod.gb"
else
  cp "${name}.gb" "${name}-step.gb"
  rest="$args_inst"
  while [[ "$rest" == *" -- "* ]]
  do
    $goto_instrument ${rest%%" -- "*} "${name}-step.gb" "${name}-step.gb"
    rest="${rest#*" -- "}"
  done
  $goto_instrument ${rest} "${name}-step.gb" "${name}-mod.gb"
  rm -f "${name}-step.gb"
fi
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
if ! echo "${args_cbmc}" | grep -q -- --function ; then
  $goto_instrument --drop-unused-functions "${name}-mod.gb" "${name}-mod.gb"
fi
$goto_instrument --show-goto-functions "${name}-mod.gb"
$cbmc "${name}-mod.gb" ${args_cbmc}
