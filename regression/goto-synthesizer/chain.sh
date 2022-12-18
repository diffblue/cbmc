#!/bin/bash

set -e

goto_cc=$1
goto_instrument=$2
goto_synthesizer=$3
cbmc=$4
is_windows=$5

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

if [[ "${is_windows}" == "true" ]]; then
  $goto_cc "${name}.c" "/Fe${name}.gb"
else
  $goto_cc -o "${name}.gb" "${name}.c"
fi

rm -f "${name}-mod.gb"
rm -f "${name}-mod-2.gb"
echo "Running goto-instrument: "
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
echo "Running goto-synthesizer: "
$goto_synthesizer "${name}-mod.gb" "${name}-mod-2.gb"
echo "Running CBMC: "
$cbmc "${name}-mod-2.gb" ${args_cbmc}
