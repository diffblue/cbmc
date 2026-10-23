#!/usr/bin/env bash

set -e

symtab2gb=$1
goto_instrument=$2
goto_cc=$3

name=${*:$#}
base=${name%.*}

rm -f "${base}.gb" "${base}.dump.c" "${base}.recompiled.gb"

# symbol table (JSON) -> goto binary -> dumped C -> recompiled goto binary
"$symtab2gb" "${name}" --out "${base}.gb"
"$goto_instrument" --dump-c "${base}.gb" "${base}.dump.c"
cat "${base}.dump.c"
"$goto_cc" -o "${base}.recompiled.gb" "${base}.dump.c"
