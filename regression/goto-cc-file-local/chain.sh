#!/usr/bin/env bash
#
# Invoke one or more CPROVER tools depending on arguments
#
# Author: Kareem Khazem <karkhaz@karkhaz.com>

set -e

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

if [[ "${is_windows}" != "true" && "${is_windows}" != "false" ]]; then
  (>&2 echo "\$is_windows should be true or false (got '" "${is_windows}" "')")
  exit 1
fi

if is_in use_find "$ALL_ARGS"; then
  SRC=$(find . -name "*.c")
else
  SRC=*.c
fi

echo "Source files are ${SRC}"

wall=""
if is_in wall "$ALL_ARGS"; then
  if [[ "${is_windows}" == "true" ]]; then
    wall="/Wall"
  else
    wall="-Wall"
  fi
fi

# Allow a test to override the default verbosity by passing "--verbosity N"
# in its arguments, e.g. to drop below the warning threshold ("--verbosity 1")
# and check that a warning is *not* shown.  Otherwise default to the verbose
# setting used by the rest of the suite.
if [[ "$ALL_ARGS" =~ --verbosity[[:space:]]+([0-9]+) ]]; then
  verbosity="--verbosity ${BASH_REMATCH[1]}"
else
  verbosity="--verbosity 10"
fi

export_flag=""
if is_in old-flag "$ALL_ARGS"; then
  export_flag="--export-function-local-symbols"
else
  export_flag="--export-file-local-symbols"
fi

OUT_FILE="main.gb"
if is_in compile-and-link "$ALL_ARGS"; then
    if [[ "${is_windows}" == "true" ]]; then
      "${goto_cc}"                        \
          ${export_flag}                  \
          ${verbosity}                  \
          ${wall}                         \
          ${suffix}                       \
          ${SRC}                          \
          "/Fe${OUT_FILE}"
  
    else
      "${goto_cc}"                        \
          ${export_flag}                  \
          ${verbosity}                  \
          ${wall}                         \
          ${suffix}                       \
          ${SRC}                          \
          -o "${OUT_FILE}"
    fi
else
  cnt=0
  for src in ${SRC}; do
    cnt=$((cnt + 1))
    out_suffix=""
    if is_in out-file-counter "$ALL_ARGS"; then
      out_suffix="_$cnt"
      if is_in suffix "$ALL_ARGS"; then
        suffix="--mangle-suffix custom_$cnt"
      fi
    fi
  
    base=${src%.c}
    OUT_FILE=$(basename "${base}${out_suffix}")".gb"
  
    if [[ "${is_windows}" == "true" ]]; then
      "${goto_cc}"                        \
          ${export_flag}                  \
          ${verbosity}                  \
          ${wall}                         \
          ${suffix}                       \
          '/c' "${base}.c"                  \
          "/Fo${OUT_FILE}"
  
    else
      "${goto_cc}"                        \
          ${export_flag}                  \
          ${verbosity}                  \
          ${wall}                         \
          ${suffix}                       \
          -c "${base}.c"                  \
          -o "${OUT_FILE}"
    fi
  done
fi

if is_in final-link "$ALL_ARGS"; then
  OUT_FILE=final-link.gb
  rm -f ${OUT_FILE}
  if [[ "${is_windows}" == "true" ]]; then
    "${goto_cc}"                        \
        ${export_flag}                  \
        ${verbosity}                  \
        ${wall}                         \
        ${suffix}                       \
        ./*.gb                          \
        "/Fe${OUT_FILE}"

  else
    "${goto_cc}"                        \
        ${export_flag}                  \
        ${verbosity}                  \
        ${wall}                         \
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
