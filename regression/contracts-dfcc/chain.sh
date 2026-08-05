#!/usr/bin/env bash

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

# When the first instrumentation argument is --char-signedness-stability,
# compile and instrument the test a second time with the opposite signedness
# of plain char, and require the resulting goto functions to be identical.
check_char_signedness_stability=0
if [[ "$args_inst" == "--char-signedness-stability"* ]]
then
  check_char_signedness_stability=1
  args_inst="${args_inst#--char-signedness-stability}"
  args_inst="${args_inst# }"
fi

# An optional pre-processing pass with goto-instrument can be requested by
# separating its arguments from the main instrumentation arguments using
# " __ ", as in: --drop-unused-functions __ --dfcc main
args_pre=""
if [[ "$args_inst" == *" __ "* ]]
then
  args_pre="${args_inst%%" __ "*}"
  args_inst="${args_inst#*" __ "}"
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
  signedness_flag=""
  if [[ "$check_char_signedness_stability" == "1" ]]; then
    signedness_flag="-fsigned-char"
  fi
  $goto_cc ${signedness_flag} -o "${name}${dfcc_suffix}.gb" "${name}.c"
fi

if [[ -n "$args_pre" ]]; then
  $goto_instrument ${args_pre} "${name}${dfcc_suffix}.gb" \
    "${name}${dfcc_suffix}-pre.gb"
  mv "${name}${dfcc_suffix}-pre.gb" "${name}${dfcc_suffix}.gb"
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
if ! echo "${args_cbmc}" | grep -q -- --function ; then
  $goto_instrument --drop-unused-functions "${name}${dfcc_suffix}-mod.gb" "${name}${dfcc_suffix}-mod.gb"
fi
if [[ "$check_char_signedness_stability" == "1" ]]
then
  $goto_cc -funsigned-char -o "${name}-uchar.gb" "${name}.c"
  $goto_instrument ${args_inst} "${name}-uchar.gb" "${name}-uchar-mod.gb"
  $goto_instrument --show-goto-functions "${name}${dfcc_suffix}-mod.gb" | \
    grep -v '^Reading' > "${name}-default.txt"
  $goto_instrument --show-goto-functions "${name}-uchar-mod.gb" | \
    grep -v '^Reading' > "${name}-uchar.txt"
  if diff "${name}-default.txt" "${name}-uchar.txt"
  then
    echo "GOTO FUNCTIONS IDENTICAL ACROSS CHAR SIGNEDNESS"
  fi
  rm "${name}-default.txt" "${name}-uchar.txt"
fi
$goto_instrument --show-goto-functions "${name}${dfcc_suffix}-mod.gb"
$cbmc --sat-solver cadical "${name}${dfcc_suffix}-mod.gb" ${args_cbmc}
