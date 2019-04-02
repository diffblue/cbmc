#!/usr/bin/env bash
#
# Invoke one or more CPROVER tools depending on arguments
#
# Author: Kareem Khazem <karkhaz@karkhaz.com>

is_in()
{
  [[ "$2" =~ $1 ]] && return 0 || return 1
}

ALL_ARGS="$@"
OUT_FILE=""

if is_in suffix "$ALL_ARGS"; then
  suffix="--mangle-suffix custom_suffix"
else
  suffix=""
fi

goto_cc=$1
goto_instrument=$2
cbmc=$3
is_windows=$4

for src in *.c; do
  base=${src%.c}
  OUT_FILE="${base}.gb"

  if [[ "${is_windows}" == "true" ]]; then
    "${goto_cc}"                        \
        /export-function-local-symbols  \
        /verbosity 10                   \
        ${suffix}                       \
        /c"${base}.c"                   \
        /Fo"${OUT_FILE}"

  elif [[ "${is_windows}" == "false" ]]; then
    "${goto_cc}"                        \
        --export-function-local-symbols \
        --verbosity 10                  \
        ${suffix}                       \
        -c "${base}.c"                  \
        -o "${OUT_FILE}"
  else
    (>&2 echo "\$is_windows should be true or false (got '" "${is_windows}" "')")
    exit 1
  fi
done

if is_in final-link "$ALL_ARGS"; then
  OUT_FILE=final-link.gb
  if [[ "${is_windows}" == "true" ]]; then
    "${goto_cc}"                        \
        /export-function-local-symbols  \
        /verbosity 10                   \
        ${suffix}                       \
        ./*.gb                          \
        /Fe "${OUT_FILE}"

  elif [[ "${is_windows}" == "false" ]]; then
    "${goto_cc}"                        \
        --export-function-local-symbols \
        --verbosity 10                  \
        ${suffix}                       \
        ./*.gb                          \
        -o "${OUT_FILE}"
  fi
fi

if is_in show-symbol-table "$ALL_ARGS"; then
  "${goto_instrument}" --show-symbol-table "${OUT_FILE}"
fi

if is_in assertion-check "$ALL_ARGS"; then
  "${cbmc}" "${OUT_FILE}"
fi
