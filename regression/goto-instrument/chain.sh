#!/bin/bash

set -e

goto_cc=$1
goto_instrument=$2
cbmc=$3
is_windows=$4

name=${*:$#}

if [[ x$name == x ]];  then
  name=${name%.c}
fi

args=${*:5:$#-5}

if [[ "${is_windows}" == "true" && x$name != x ]]; then
  $goto_cc "main.gb" ${name}
  name="main"
  mv "${name}.exe" "${name}.gb"
elif [[ "${is_windows}" == "true" ]]; then
  $goto_cc "${name}.c"
  mv "${name}.exe" "${name}.gb"
elif [[ x$name != x ]]; then
  $goto_cc -o "main.gb" ${name}
  echo "name: ${name}"
  name="main"
else
  $goto_cc -o "${name}.gb" "${name}.c"
fi

rm -f "${name}-mod.gb"
$goto_instrument ${args} "${name}.gb" "${name}-mod.gb"
if [ ! -e "${name}-mod.gb" ] ; then
  cp "$name.gb" "${name}-mod.gb"
elif echo $args | grep -q -- "--dump-c-type-header" ; then
  cat "${name}-mod.gb"
  mv "${name}.gb" "${name}-mod.gb"
elif echo $args | grep -q -- "--dump-c" ; then
  mv "${name}-mod.gb" "${name}-mod.c"

  if [[ "${is_windows}" == "true" ]]; then
    $goto_cc "${name}-mod.c"
    mv "${name}-mod.exe" "${name}-mod.gb"
  else
    $goto_cc -o "${name}-mod.gb" "${name}-mod.c"
  fi

  rm "${name}-mod.c"
fi
$goto_instrument --show-goto-functions "${name}-mod.gb"
$cbmc "${name}-mod.gb"
