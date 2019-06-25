#!/usr/bin/env bash
#
# Invoke one or more CPROVER tools depending on arguments
#
# Author: Kareem Khazem <karkhaz@karkhaz.com>

set -e

goto_cc=$1
goto_instrument=$2
cbmc=$3
is_windows=$4

if [[ "${is_windows}" != "true" && "${is_windows}" != "false" ]]; then
  (>&2 echo "\$is_windows should be true or false (got '" "${is_windows}" "')")
  exit 1
fi

if [[ "${is_windows}" == "true" ]]; then
  export DASH_C='/c'
  export DASH_O='/Fo'
  export DASH_E='/Fe'
else
  export DASH_C='-c'
  export DASH_O='-o'
  export DASH_E='-o'
fi


OUT_FILE=out-link.gb
FUNCTION_SRC=function.c
FUNCTION_DST=function.gb
STUB_FILE=stub.c
HARNESS_SRC=harness.c
rm -f "${OUT_FILE}" "${STUB_FILE}"

"${goto_cc}"                        \
      --verbosity 10                  \
      "${DASH_C}" "${FUNCTION_SRC}"           \
      "${DASH_O}" "${FUNCTION_DST}"

"${goto_instrument}" \
    --verbosity 10 \
    --contract-to-stub stub \
    "${FUNCTION_DST}" \
    "${STUB_FILE}"
    
"${goto_cc}"                        \
    --verbosity 10                  \
    -I ../                          \
    "${STUB_FILE}"                          \
    "${HARNESS_SRC}"               \
    "${DASH_E}" "${OUT_FILE}"


"${cbmc}" "${OUT_FILE}"
