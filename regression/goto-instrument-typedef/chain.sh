#!/bin/bash

GC=$1
GI=$2
is_windows=$3

name=${*:$#}
name=${name%.c}

args=${*:4:$#-4}

rm "${name}.gb"
if [[ "${is_windows}" == "true" ]]; then
  "$GC" "${name}.c" --function fun
  mv "${name}.exe" "${name}.gb"
else
  "$GC" "${name}.c" --function fun -o "${name}.gb"
fi

echo "$GI" ${args} "${name}.gb"
"$GI" ${args} "${name}.gb"
